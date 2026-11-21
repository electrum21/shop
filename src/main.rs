mod pq;

use memchr::memchr;
use memmap2::Mmap;
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering::*};
use std::thread;
use xxhash_rust::xxh3::xxh3_64;

const DAY: i64 = 86_400_000;
const WEEK: i64 = 7 * DAY;
const GAP: i64 = 1_800_000;
const NBE: usize = 512;
const NBP: usize = 4096;
const CHUNK: usize = 4 << 20;
const NONE_CAT: u16 = u16::MAX;

type Bytes = &'static [u8];

#[inline(always)]
fn h64(b: &[u8]) -> u64 {
    let h = xxh3_64(b);
    if h == 0 || h == u64::MAX {
        1
    } else {
        h
    }
}
#[inline(always)]
fn mkref(s: &[u8]) -> u64 {
    (s.as_ptr() as u64) | ((s.len().min(0xFFFF) as u64) << 48)
}
#[inline(always)]
fn deref(r: u64) -> &'static [u8] {
    unsafe { std::slice::from_raw_parts((r & 0x0000_FFFF_FFFF_FFFF) as *const u8, (r >> 48) as usize) }
}
#[inline(always)]
fn prefix8(s: &[u8]) -> u64 {
    let mut b = [0u8; 8];
    let n = s.len().min(8);
    b[..n].copy_from_slice(&s[..n]);
    u64::from_be_bytes(b)
}

// ---------------------------------------------------------------- hashing for std maps
#[derive(Default)]
struct FastHasher(u64);
impl Hasher for FastHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        self.0 = (self.0.rotate_left(5) ^ xxh3_64(bytes)).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }
    fn write_usize(&mut self, i: usize) {
        self.0 = (self.0.rotate_left(5) ^ i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }
}
type FMap<K, V> = HashMap<K, V, BuildHasherDefault<FastHasher>>;

// ---------------------------------------------------------------- CSV
use std::arch::x86_64::*;

#[inline(always)]
unsafe fn masks<const AVX: bool>(p: *const u8) -> (u64, u64, u64) {
    if AVX {
        let lo = _mm256_loadu_si256(p as *const __m256i);
        let hi = _mm256_loadu_si256(p.add(32) as *const __m256i);
        let vn = _mm256_set1_epi8(b'\n' as i8);
        let vc = _mm256_set1_epi8(b',' as i8);
        let vq = _mm256_set1_epi8(b'"' as i8);
        let m = |v: __m256i, w: __m256i| -> u64 {
            (_mm256_movemask_epi8(_mm256_cmpeq_epi8(v, w)) as u32 as u64)
        };
        (
            m(lo, vn) | (m(hi, vn) << 32),
            m(lo, vc) | (m(hi, vc) << 32),
            m(lo, vq) | (m(hi, vq) << 32),
        )
    } else {
        let v0 = _mm_loadu_si128(p as *const __m128i);
        let v1 = _mm_loadu_si128(p.add(16) as *const __m128i);
        let v2 = _mm_loadu_si128(p.add(32) as *const __m128i);
        let v3 = _mm_loadu_si128(p.add(48) as *const __m128i);
        let mk = |c: u8| -> u64 {
            let w = _mm_set1_epi8(c as i8);
            let g = |v: __m128i| _mm_movemask_epi8(_mm_cmpeq_epi8(v, w)) as u32 as u64;
            g(v0) | (g(v1) << 16) | (g(v2) << 32) | (g(v3) << 48)
        };
        (mk(b'\n'), mk(b','), mk(b'"'))
    }
}

/// Validate quoting of a complete record and strip quotes.
#[inline(always)]
unsafe fn finish_fields<const N: usize>(out: &mut [&'static [u8]; N], quotes: u32) -> bool {
    if quotes != 0 {
        let mut qf = 0u32;
        for f in out.iter_mut() {
            let n = f.len();
            if n >= 2 && *f.get_unchecked(0) == b'"' && *f.get_unchecked(n - 1) == b'"' {
                qf += 1;
                *f = f.get_unchecked(1..n - 1);
            }
        }
        if quotes != 2 * qf {
            return false;
        }
    }
    true
}

#[inline(always)]
unsafe fn drive<const AVX: bool, const N: usize, F: FnMut(&[&'static [u8]; N])>(d: &'static [u8], f: &mut F) {
    let n = d.len();
    let mut fields: [&'static [u8]; N] = [&[]; N];
    let mut k = 0usize;
    let mut fs = 0usize;
    let mut bad = false;
    let mut qcum: u32 = 0;
    let mut qline: u32 = 0;
    let mut base = 0usize;
    let mut tail = [0u8; 64];
    while base < n {
        let p = if base + 64 <= n {
            d.as_ptr().add(base)
        } else {
            let r = n - base;
            tail[..r].copy_from_slice(&d[base..]);
            tail.as_ptr()
        };
        let (mn, mc, mq) = masks::<AVX>(p);
        let mut s = mn | mc;
        while s != 0 {
            let b = s.trailing_zeros();
            s &= s - 1;
            let pos = base + b as usize;
            if (mn >> b) & 1 != 0 {
                let qb = qcum + (mq & ((1u64 << b) - 1)).count_ones();
                if k == N - 1 && !bad {
                    *fields.get_unchecked_mut(N - 1) = d.get_unchecked(fs..pos);
                    if finish_fields::<N>(&mut fields, qb - qline) {
                        f(&fields);
                    }
                }
                k = 0;
                bad = false;
                fs = pos + 1;
                qline = qb;
            } else if k < N - 1 {
                *fields.get_unchecked_mut(k) = d.get_unchecked(fs..pos);
                k += 1;
                fs = pos + 1;
            } else {
                bad = true;
            }
        }
        qcum += mq.count_ones();
        base += 64;
    }
    if fs < n || k > 0 {
        if k == N - 1 && !bad {
            fields[N - 1] = &d[fs..n];
            if finish_fields::<N>(&mut fields, qcum - qline) {
                f(&fields);
            }
        }
    }
}

#[target_feature(enable = "avx2,bmi1,popcnt")]
unsafe fn drive_avx2<const N: usize, F: FnMut(&[&'static [u8]; N])>(d: &'static [u8], f: &mut F) {
    drive::<true, N, F>(d, f)
}

#[inline(always)]
fn for_recs<const N: usize>(d: &'static [u8], mut f: impl FnMut(&[&'static [u8]; N])) {
    unsafe {
        if is_x86_feature_detected!("avx2") && is_x86_feature_detected!("popcnt") && is_x86_feature_detected!("bmi1") {
            drive_avx2::<N, _>(d, &mut f)
        } else {
            drive::<false, N, _>(d, &mut f)
        }
    }
}

// ---------------------------------------------------------------- timestamps
#[inline(always)]
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let mp = (m + 9) % 12;
    let doy = (153 * mp + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468
}
#[inline(always)]
fn num(f: &[u8], s: usize, l: usize) -> Option<i64> {
    let mut v = 0i64;
    for &b in &f[s..s + l] {
        let d = b.wrapping_sub(b'0');
        if d > 9 {
            return None;
        }
        v = v * 10 + d as i64;
    }
    Some(v)
}
#[inline(always)]
fn parse8(chunk: u64) -> Option<u64> {
    // all eight bytes ASCII digits?
    if ((chunk & 0xF0F0_F0F0_F0F0_F0F0) | (((chunk.wrapping_add(0x0606_0606_0606_0606)) & 0xF0F0_F0F0_F0F0_F0F0) >> 4))
        != 0x3333_3333_3333_3333
    {
        return None;
    }
    let mut v = chunk;
    v = (v & 0x0F0F_0F0F_0F0F_0F0F).wrapping_mul(2561) >> 8;
    v = (v & 0x00FF_00FF_00FF_00FF).wrapping_mul(6_553_601) >> 16;
    v = (v & 0x0000_FFFF_0000_FFFF).wrapping_mul(42_949_672_960_001) >> 32;
    Some(v)
}
#[inline(always)]
fn parse_ms(f: &[u8]) -> Option<i64> {
    let n = f.len();
    if n == 0 {
        return None;
    }
    if n <= 18 {
        let mut acc: u64 = 0;
        let mut i = 0;
        if n >= 8 {
            acc = parse8(u64::from_le_bytes(f[0..8].try_into().unwrap()))?;
            i = 8;
        }
        let mut bad = 0u8;
        while i < n {
            let d = f[i].wrapping_sub(b'0');
            bad |= (d > 9) as u8;
            acc = acc * 10 + d as u64;
            i += 1;
        }
        return if bad != 0 { None } else { Some(acc as i64) };
    }
    let mut acc: u64 = 0;
    for &b in f {
        let d = b.wrapping_sub(b'0');
        if d > 9 {
            return None;
        }
        acc = acc.checked_mul(10)?.checked_add(d as u64)?;
    }
    if acc > i64::MAX as u64 {
        None
    } else {
        Some(acc as i64)
    }
}

pub struct DCache {
    k1: [u64; 128],
    k2: [u16; 128],
    days: [i64; 128],
}
impl DCache {
    fn new() -> Self {
        DCache { k1: [0; 128], k2: [0; 128], days: [0; 128] }
    }
}

#[inline(always)]
fn parse_ts(f: &[u8], c: &mut DCache) -> Option<i64> {
    let n = f.len();
    if (n == 20 || n == 25) && f[4] == b'-' {
        parse_iso(f, c)
    } else {
        parse_ms(f)
    }
}
#[inline(always)]
fn parse_iso(f: &[u8], c: &mut DCache) -> Option<i64> {
    let n = f.len();
    if f[10] != b'T' || f[13] != b':' || f[16] != b':' {
        return None;
    }
    let k1 = u64::from_le_bytes(f[0..8].try_into().unwrap());
    let k2 = u16::from_le_bytes([f[8], f[9]]);
    let idx = ((f[9] as usize) ^ ((f[8] as usize) << 2) ^ ((f[6] as usize) << 4) ^ ((f[3] as usize) << 6)) & 127;
    let days = if c.k1[idx] == k1 && c.k2[idx] == k2 {
        c.days[idx]
    } else {
        let days = parse_date(f)?;
        c.k1[idx] = k1;
        c.k2[idx] = k2;
        c.days[idx] = days;
        days
    };
    let mut bad = 0u8;
    let mut dg = |i: usize| -> i64 {
        let v = f[i].wrapping_sub(b'0');
        bad |= (v > 9) as u8;
        v as i64
    };
    let h = dg(11) * 10 + dg(12);
    let mi = dg(14) * 10 + dg(15);
    let s = dg(17) * 10 + dg(18);
    let mut off = 0i64;
    if n == 20 {
        if f[19] != b'Z' {
            return None;
        }
    } else {
        let sign = match f[19] {
            b'+' => 1,
            b'-' => -1,
            _ => return None,
        };
        if f[22] != b':' {
            return None;
        }
        let oh = dg(20) * 10 + dg(21);
        let om = dg(23) * 10 + dg(24);
        if oh > 23 || om > 59 {
            return None;
        }
        off = sign * (oh * 60 + om) * 60_000;
    }
    if bad != 0 || h > 23 || mi > 59 || s > 59 {
        return None;
    }
    Some((days * 86_400 + h * 3600 + mi * 60 + s) * 1000 - off)
}
#[cold]
fn parse_date(f: &[u8]) -> Option<i64> {
    if f[4] != b'-' || f[7] != b'-' {
        return None;
    }
    let y = num(f, 0, 4)?;
    let mo = num(f, 5, 2)?;
    let d = num(f, 8, 2)?;
    if !(1..=12).contains(&mo) || d < 1 {
        return None;
    }
    let leap = (y % 4 == 0 && y % 100 != 0) || y % 400 == 0;
    let dim = match mo {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        _ => {
            if leap {
                29
            } else {
                28
            }
        }
    };
    if d > dim {
        return None;
    }
    Some(days_from_civil(y, mo, d))
}

// ---------------------------------------------------------------- files
fn csv_files(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = match std::fs::read_dir(dir) {
        Ok(rd) => rd
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|p| p.extension().map_or(false, |x| x == "csv") && p.is_file())
            .collect(),
        Err(_) => vec![],
    };
    v.sort();
    v
}

fn map_file(p: &Path) -> Bytes {
    let f = std::fs::File::open(p).expect("open");
    let len = f.metadata().map(|m| m.len()).unwrap_or(0);
    if len == 0 {
        return &[];
    }
    let m = unsafe { Mmap::map(&f).expect("mmap") };
    let m: &'static Mmap = Box::leak(Box::new(m));
    &m[..]
}

#[derive(Clone, Copy)]
struct Chunk {
    file: Bytes,
    start: usize,
    end: usize,
    kind: u8,
}

fn boundary(d: &[u8], b: usize) -> usize {
    if b == 0 {
        return 0;
    }
    if b >= d.len() {
        return d.len();
    }
    match memchr(b'\n', &d[b - 1..]) {
        Some(i) => b - 1 + i + 1,
        None => d.len(),
    }
}

fn make_chunks(files: &[Bytes], kind: u8, out: &mut Vec<Chunk>) {
    for &d in files {
        if d.is_empty() {
            continue;
        }
        // skip header line
        let hdr = match memchr(b'\n', d) {
            Some(i) => i + 1,
            None => continue,
        };
        let nch = (d.len() + CHUNK - 1) / CHUNK;
        for c in 0..nch {
            let s = boundary(d, c * CHUNK).max(hdr);
            let e = boundary(d, (c + 1) * CHUNK);
            if s < e {
                out.push(Chunk { file: d, start: s, end: e, kind });
            }
        }
    }
}

fn read_small(p: &Path) -> Bytes {
    let v = std::fs::read(p).unwrap_or_default();
    Box::leak(v.into_boxed_slice())
}

// ---------------------------------------------------------------- link table (concurrent union-find)
#[repr(C, align(32))]
struct Slot {
    key: AtomicU64,
    rf: AtomicU64,
    pre: AtomicU64,
    parent: AtomicU32, // 0 = root, else slot+1
    _p: u32,
}
const RESERVED: u64 = u64::MAX;

struct LinkTable {
    s: Box<[Slot]>,
    mask: usize,
}

impl LinkTable {
    fn new(cap: usize) -> Self {
        let cap = cap.next_power_of_two().max(16);
        let bytes = cap * std::mem::size_of::<Slot>();
        let s = unsafe {
            let p = map_zero(bytes) as *mut Slot;
            Box::from_raw(std::slice::from_raw_parts_mut(p, cap))
        };
        LinkTable { s, mask: cap - 1 }
    }
    fn insert(&self, h: u64, rf: u64) -> usize {
        let mut i = (h as usize) & self.mask;
        loop {
            let k = self.s[i].key.load(Acquire);
            if k == h {
                return i;
            }
            if k == 0 {
                if self.s[i].key.compare_exchange(0, RESERVED, AcqRel, Acquire).is_ok() {
                    self.s[i].rf.store(rf, Relaxed);
                    self.s[i].pre.store(prefix8(deref(rf)), Relaxed);
                    self.s[i].key.store(h, Release);
                    return i;
                }
                continue;
            }
            if k == RESERVED {
                std::hint::spin_loop();
                continue;
            }
            i = (i + 1) & self.mask;
        }
    }
    fn find(&self, mut x: usize) -> usize {
        loop {
            let p = self.s[x].parent.load(Relaxed);
            if p == 0 {
                return x;
            }
            let p = (p - 1) as usize;
            let gp = self.s[p].parent.load(Relaxed);
            if gp != 0 {
                let _ = self.s[x].parent.compare_exchange(p as u32 + 1, gp, Relaxed, Relaxed);
            }
            x = p;
        }
    }
    fn less(&self, a: usize, b: usize) -> bool {
        let pa = self.s[a].pre.load(Relaxed);
        let pb = self.s[b].pre.load(Relaxed);
        if pa != pb {
            return pa < pb;
        }
        deref(self.s[a].rf.load(Relaxed)) < deref(self.s[b].rf.load(Relaxed))
    }
    fn union(&self, a: usize, b: usize) {
        loop {
            let ra = self.find(a);
            let rb = self.find(b);
            if ra == rb {
                return;
            }
            let (lo, hi) = if self.less(ra, rb) { (ra, rb) } else { (rb, ra) };
            if self.s[hi].parent.compare_exchange(0, lo as u32 + 1, AcqRel, Relaxed).is_ok() {
                return;
            }
        }
    }
    /// After flatten: (person key, person name ref)
    #[inline(always)]
    fn lookup(&self, h: u64) -> Option<(u64, u64)> {
        let mut i = (h as usize) & self.mask;
        loop {
            let sl = &self.s[i];
            let k = sl.key.load(Relaxed);
            if k == h {
                return Some((sl.pre.load(Relaxed), sl.rf.load(Relaxed)));
            }
            if k == 0 {
                return None;
            }
            i = (i + 1) & self.mask;
        }
    }
    #[inline(always)]
    fn prefetch(&self, h: u64) {
        unsafe {
            _mm_prefetch(self.s.as_ptr().add((h as usize) & self.mask) as *const i8, _MM_HINT_T0);
        }
    }
    fn flatten_range(&self, lo: usize, hi: usize) {
        for i in lo..hi {
            let k = self.s[i].key.load(Relaxed);
            if k == 0 {
                continue;
            }
            let r = self.find(i);
            if r == i {
                self.s[i].pre.store(k, Relaxed);
            } else {
                let rk = self.s[r].key.load(Relaxed);
                let rr = self.s[r].rf.load(Relaxed);
                self.s[i].pre.store(rk, Relaxed);
                self.s[i].rf.store(rr, Relaxed);
            }
        }
    }
}

// ---------------------------------------------------------------- block pool
const BLK: usize = 8192;
const SEG: usize = 8 << 20;

fn map_zero(size: usize) -> usize {
    unsafe {
        let align = 2usize << 20;
        let total = size + align;
        let p = libc::mmap(
            std::ptr::null_mut(),
            total,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE,
            -1,
            0,
        );
        assert!(p != libc::MAP_FAILED, "mmap failed");
        let a = ((p as usize) + align - 1) & !(align - 1);
        libc::madvise(a as *mut libc::c_void, size, libc::MADV_HUGEPAGE);
        a
    }
}

fn map_huge(size: usize) -> usize {
    unsafe {
        let align = 2usize << 20;
        let total = size + align;
        let p = libc::mmap(
            std::ptr::null_mut(),
            total,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE,
            -1,
            0,
        );
        assert!(p != libc::MAP_FAILED, "mmap failed");
        let a = ((p as usize) + align - 1) & !(align - 1);
        libc::madvise(a as *mut libc::c_void, size, libc::MADV_HUGEPAGE);
        libc::madvise(a as *mut libc::c_void, size, 23); // MADV_POPULATE_WRITE (best effort)
        a
    }
}

thread_local! {
    static ARENA: std::cell::Cell<(usize, usize)> = const { std::cell::Cell::new((0, 0)) };
}

struct Pool {
    free: Mutex<Vec<usize>>,
    nfree: AtomicUsize,
}
impl Pool {
    fn new() -> Self {
        Pool { free: Mutex::new(Vec::new()), nfree: AtomicUsize::new(0) }
    }
    fn alloc(&self) -> usize {
        if self.nfree.load(Relaxed) > 0 {
            let mut f = self.free.lock().unwrap();
            if let Some(p) = f.pop() {
                self.nfree.store(f.len(), Relaxed);
                return p;
            }
        }
        ARENA.with(|a| {
            let (cur, end) = a.get();
            if cur + BLK <= end {
                a.set((cur + BLK, end));
                cur
            } else {
                let p = map_huge(SEG);
                a.set((p + BLK, p + SEG));
                p
            }
        })
    }
    fn free_all(&self, blocks: &[usize]) {
        let mut f = self.free.lock().unwrap();
        f.extend_from_slice(blocks);
        self.nfree.store(f.len(), Relaxed);
    }
}

struct BW<T> {
    cur: *mut T,
    end: *mut T,
    blocks: Vec<usize>,
    n: u64,
}
unsafe impl<T> Send for BW<T> {}
unsafe impl<T> Sync for BW<T> {}
impl<T: Copy> BW<T> {
    const PER: usize = BLK / std::mem::size_of::<T>();
    fn new() -> Self {
        BW { cur: std::ptr::null_mut(), end: std::ptr::null_mut(), blocks: Vec::new(), n: 0 }
    }
    #[inline(always)]
    fn push(&mut self, v: T, pool: &Pool) {
        if self.cur == self.end {
            self.grow(pool);
        }
        unsafe {
            self.cur.write(v);
            self.cur = self.cur.add(1);
        }
        self.n += 1;
    }
    #[cold]
    #[inline(never)]
    fn grow(&mut self, pool: &Pool) {
        let b = pool.alloc() as *mut T;
        self.blocks.push(b as usize);
        self.cur = b;
        self.end = unsafe { b.add(Self::PER) };
    }
    fn len(&self) -> usize {
        match self.blocks.last() {
            None => 0,
            Some(&l) => (self.blocks.len() - 1) * Self::PER + (self.cur as usize - l) / std::mem::size_of::<T>(),
        }
    }
    fn for_slices(&self, mut f: impl FnMut(&[T])) {
        let nb = self.blocks.len();
        for (i, &b) in self.blocks.iter().enumerate() {
            let n = if i + 1 < nb { Self::PER } else { (self.cur as usize - b) / std::mem::size_of::<T>() };
            f(unsafe { std::slice::from_raw_parts(b as *const T, n) });
        }
    }
}

// ---------------------------------------------------------------- records
/// Surviving-candidate event in a person bucket (24 bytes).
/// packed: ts_rel(32, relative to window start) << 32 | cat(6) << 26 | kind(2) << 24 | price(24)
#[derive(Clone, Copy)]
#[repr(C)]
struct PEv {
    pkey: u64,
    nref: u64,
    packed: u64,
}
/// Click in a person bucket (24 bytes). tc: ts_rel(32, relative to window start - 7 days) << 32 | campaign
#[derive(Clone, Copy)]
#[repr(C)]
struct CRec {
    pkey: u64,
    idref: u64,
    tc: u64,
}
/// Dedup record (24 bytes): one per parsed event line. loc = 0 for an invalid copy, else
/// 1<<63 | pbucket << 48 | worker << 40 | index of its PEv in that worker's bucket writer.
#[derive(Clone, Copy)]
#[repr(C)]
struct DR {
    eid: u64,
    loc: u64,
    ingest: u32,
    _p: u32,
}
#[derive(Clone, Copy)]
struct ETmp {
    eid: u64,
    uh: u64,
    uref: u64,
    packed: u64,
    ingest: u32,
}

struct Ctx {
    ws: i64,
    we: i64,
    base_day: i64,
    nd: usize,
    products: FMap<&'static [u8], u16>,
    camps: FMap<&'static [u8], u32>,
    ncamp: usize,
    unknown_id: u16,
    links: LinkTable,
    nthreads: usize,
}

struct W1 {
    pe: Vec<BW<PEv>>,
    dr: Vec<BW<DR>>,
    cb: Vec<BW<CRec>>,
    pool: &'static Pool,
    dc: DCache,
    wid: u64,
    ebatch: Vec<ETmp>,
    cbatch: Vec<(u64, u64, u64)>,
}

#[inline(always)]
fn ebucket(eid: u64) -> usize {
    ((eid >> 20) as usize) & (NBE - 1)
}
#[inline(always)]
fn pbucket(pkey: u64) -> usize {
    ((pkey >> 24) as usize) & (NBP - 1)
}

#[inline(always)]
fn parse_event(f: &[&'static [u8]; 7], ctx: &Ctx, w: &mut W1) {
    let eidb = f[0];
    if eidb.is_empty() {
        return;
    }
    let eid = h64(eidb);
    let ing_ms = parse_ts(f[3], &mut w.dc);
    let ingest = match ing_ms {
        Some(v) if v >= 0 => (v / 1000).min(u32::MAX as i64 - 1) as u32,
        _ => u32::MAX,
    };
    'v: {
        let uidb = f[1];
        if uidb.is_empty() {
            break 'v;
        }
        let Some(ts) = parse_ts(f[2], &mut w.dc) else { break 'v };
        if ts < ctx.ws || ts >= ctx.we {
            break 'v;
        }
        let kind = match f[4] {
            b"view" => 0u64,
            b"cart" => 1,
            b"purchase" => 2,
            _ => break 'v,
        };
        if f[5].is_empty() {
            break 'v;
        }
        let Some(im) = ing_ms else { break 'v };
        if im - ts > DAY {
            break 'v;
        }
        let mut price = 0u64;
        let mut cat = 0u64;
        if kind == 2 {
            let p = f[6];
            if p.is_empty() || !p.iter().all(|b| b.is_ascii_digit()) {
                break 'v;
            }
            let mut v = 0u64;
            for &b in p {
                v = (v * 10 + (b - b'0') as u64).min(1_000_000_000);
            }
            if v < 1 || v > 10_000_000 {
                break 'v;
            }
            price = v;
            cat = *ctx.products.get(f[5]).unwrap_or(&ctx.unknown_id) as u64;
        }
        let uh = h64(uidb);
        ctx.links.prefetch(uh);
        let packed = (((ts - ctx.ws) as u64) << 32) | (cat << 26) | (kind << 24) | price;
        w.ebatch.push(ETmp { eid, uh, uref: mkref(uidb), packed, ingest });
        if w.ebatch.len() >= 32 {
            flush_events(ctx, w);
        }
        return;
    }
    w.dr[ebucket(eid)].push(DR { eid, loc: 0, ingest, _p: 0 }, w.pool);
}

#[inline(never)]
fn flush_events(ctx: &Ctx, w: &mut W1) {
    let mut b = std::mem::take(&mut w.ebatch);
    for t in b.iter() {
        let (pkey, nref) = match ctx.links.lookup(t.uh) {
            Some(x) => x,
            None => (t.uh, t.uref),
        };
        let pb = pbucket(pkey);
        let idx = w.pe[pb].n;
        w.pe[pb].push(PEv { pkey, nref, packed: t.packed }, w.pool);
        let loc = (1u64 << 63) | ((pb as u64) << 48) | (w.wid << 40) | idx;
        w.dr[ebucket(t.eid)].push(DR { eid: t.eid, loc, ingest: t.ingest, _p: 0 }, w.pool);
    }
    b.clear();
    w.ebatch = b;
}

#[inline(always)]
fn parse_click(f: &[&'static [u8]; 4], ctx: &Ctx, w: &mut W1) {
    if f[0].is_empty() || f[1].is_empty() {
        return;
    }
    let Some(ts) = parse_ts(f[3], &mut w.dc) else { return };
    if ts < ctx.ws - WEEK || ts >= ctx.we {
        return;
    }
    let Some(&camp) = ctx.camps.get(f[2]) else { return };
    let uh = h64(f[1]);
    ctx.links.prefetch(uh);
    let tc = (((ts - (ctx.ws - WEEK)) as u64) << 32) | camp as u64;
    w.cbatch.push((uh, mkref(f[0]), tc));
    if w.cbatch.len() >= 32 {
        flush_clicks(ctx, w);
    }
}

#[inline(never)]
fn flush_clicks(ctx: &Ctx, w: &mut W1) {
    let mut b = std::mem::take(&mut w.cbatch);
    for &(uh, idref, tc) in b.iter() {
        let pkey = match ctx.links.lookup(uh) {
            Some((p, _)) => p,
            None => uh,
        };
        w.cb[pbucket(pkey)].push(CRec { pkey, idref, tc }, w.pool);
    }
    b.clear();
    w.cbatch = b;
}

// ---------------------------------------------------------------- stage 3 state
struct URows {
    nref: Vec<u64>,
    day: Vec<i32>,
    sessions: Vec<i32>,
    events: Vec<i32>,
    rev: Vec<i64>,
    top: Vec<u16>,
}
#[derive(Clone, Copy, Default)]
struct CAcc {
    sessions: u32,
    purch: u32,
    assisted: u32,
    rev: u64,
}

struct S3 {
    ur: URows,
    acc: Vec<CAcc>,
    ev: Vec<PEv>,
    ck: Vec<CRec>,
    starts: Vec<i64>,
    days: Vec<u16>,
    srev: Vec<u64>,
    runs: Vec<(u16, u32)>,
    cs: Vec<(u32, i64)>,
    catacc: Vec<(u16, u64)>,
}

#[inline(always)]
fn flush_user(st: &mut S3, name: u64, day: i64, ses: u32, evs: u32, rev: u64) {
    let mut top = NONE_CAT;
    let mut best = 0u64;
    for &(c, s) in &st.catacc {
        if s > best || (s == best && c < top) {
            best = s;
            top = c;
        }
    }
    let u = &mut st.ur;
    u.nref.push(name);
    u.day.push((day) as i32);
    u.sessions.push(ses as i32);
    u.events.push(evs as i32);
    u.rev.push(rev as i64);
    u.top.push(top);
}

fn process_person(evs: &[PEv], cks: &[CRec], ctx: &Ctx, st: &mut S3) {
    let nd = ctx.nd;
    let organic = ctx.ncamp;
    st.starts.clear();
    st.days.clear();
    st.srev.clear();
    st.runs.clear();
    st.catacc.clear();
    let name = evs[0].nref;
    let mut prev = 0i64;
    let mut cur_day: i64 = -1;
    let (mut us, mut ue, mut ur) = (0u32, 0u32, 0u64);
    for e in evs {
        let ets = ctx.ws + (e.packed >> 32) as i64;
        if st.starts.is_empty() || ets - prev > GAP {
            let d = ets.div_euclid(DAY) - ctx.base_day;
            if d != cur_day {
                if cur_day >= 0 {
                    flush_user(st, name, cur_day + ctx.base_day, us, ue, ur);
                }
                cur_day = d;
                us = 0;
                ue = 0;
                ur = 0;
                st.catacc.clear();
                st.runs.push((d as u16, st.starts.len() as u32));
            }
            us += 1;
            st.starts.push(ets);
            st.days.push(d as u16);
            st.srev.push(0);
        }
        prev = ets;
        ue += 1;
        if (e.packed >> 24) & 3 == 2 {
            let p = e.packed & 0xFF_FFFF;
            let cat = ((e.packed >> 26) & 63) as u16;
            ur += p;
            *st.srev.last_mut().unwrap() += p;
            match st.catacc.iter_mut().find(|x| x.0 == cat) {
                Some(x) => x.1 += p,
                None => st.catacc.push((cat, p)),
            }
        }
    }
    flush_user(st, name, cur_day + ctx.base_day, us, ue, ur);

    let n = st.starts.len();
    // credit
    let cbase = ctx.ws - WEEK;
    let cts = |c: &CRec| -> i64 { cbase + (c.tc >> 32) as i64 };
    let (mut lo, mut hi) = (0usize, 0usize);
    for s in 0..n {
        let t = st.starts[s];
        while hi < cks.len() && cts(&cks[hi]) <= t {
            hi += 1;
        }
        let lb = t - WEEK;
        while lo < hi && cts(&cks[lo]) < lb {
            lo += 1;
        }
        let camp = if hi > lo {
            let top_ts = cts(&cks[hi - 1]);
            let mut best = hi - 1;
            let mut k = hi - 1;
            while k > lo {
                k -= 1;
                if cts(&cks[k]) != top_ts {
                    break;
                }
                if deref(cks[k].idref) < deref(cks[best].idref) {
                    best = k;
                }
            }
            (cks[best].tc as u32) as usize
        } else {
            organic
        };
        let a = &mut st.acc[camp * nd + st.days[s] as usize];
        a.sessions += 1;
        let r = st.srev[s];
        if r > 0 {
            a.purch += 1;
            a.rev += r;
        }
    }
    // assists
    if !cks.is_empty() {
        st.cs.clear();
        for c in cks {
            st.cs.push((c.tc as u32, cts(c)));
        }
        st.cs.sort_unstable();
        let first = st.starts[0];
        let last = st.starts[n - 1];
        let mut i0 = 0;
        while i0 < st.cs.len() {
            let camp = st.cs[i0].0;
            let mut i1 = i0;
            while i1 < st.cs.len() && st.cs[i1].0 == camp {
                i1 += 1;
            }
            let mut end = 0usize;
            for k in i0..i1 {
                let t = st.cs[k].1;
                if t > last || t + WEEK < first {
                    continue;
                }
                let i = st.starts.partition_point(|&s| s < t);
                let j = st.starts.partition_point(|&s| s <= t + WEEK);
                let x = i.max(end);
                if j > x {
                    // add range [x, j)
                    let mut r = st.runs.partition_point(|r| (r.1 as usize) <= x) - 1;
                    let mut pos = x;
                    while pos < j {
                        let seg_end = if r + 1 < st.runs.len() { st.runs[r + 1].1 as usize } else { n };
                        let take = seg_end.min(j) - pos;
                        st.acc[camp as usize * nd + st.runs[r].0 as usize].assisted += take as u32;
                        pos += take;
                        r += 1;
                    }
                    end = j;
                }
            }
            i0 = i1;
        }
    }
}

// ---------------------------------------------------------------- manifest
fn parse_manifest(s: &str) -> (i64, i64) {
    let get = |key: &str| -> i64 {
        let i = s.find(key).expect("manifest key");
        let rest = &s[i + key.len()..];
        let rest = &rest[rest.find(':').unwrap()..];
        let q1 = rest.find('"').unwrap();
        let rest = &rest[q1 + 1..];
        let q2 = rest.find('"').unwrap();
        parse_ts(rest[..q2].as_bytes(), &mut DCache::new()).expect("manifest ts")
    };
    (get("window_start"), get("window_end"))
}

fn write_file(p: &Path, data: &[u8]) {
    std::fs::write(p, data).expect("write");
}

fn main() {
    let env = |k: &str, d: &str| std::env::var(k).unwrap_or_else(|_| d.to_string());
    let data = PathBuf::from(env("DATA_DIR", "/data"));
    let out = PathBuf::from(env("OUTPUT_DIR", "/output"));
    let nthreads: usize = std::env::var("NCPU")
        .ok()
        .and_then(|v| v.parse().ok())
        .filter(|&v: &usize| v > 0)
        .unwrap_or_else(|| thread::available_parallelism().map_or(4, |n| n.get()));
    let nthreads = nthreads.min(255);
    let verbose = std::env::var("VERBOSE").is_ok();
    let t0 = std::time::Instant::now();
    let lap = |name: &str| {
        if verbose {
            eprintln!("[{:7.3}s] {}", t0.elapsed().as_secs_f64(), name);
        }
    };

    let manifest = std::fs::read_to_string(data.join("manifest.json")).expect("manifest");
    let (ws, we) = parse_manifest(&manifest);
    assert!(we > ws && (we - ws) + WEEK < (1i64 << 32), "window too long for compact timestamps");
    let base_day = ws.div_euclid(DAY);
    let nd = ((we - 1).div_euclid(DAY) - base_day + 1) as usize;

    // products / campaigns
    let mut cat_names: Vec<Vec<u8>> = vec![];
    let mut prod_raw: Vec<(&'static [u8], Vec<u8>)> = vec![];
    {
        let d = read_small(&data.join("products.csv"));
        let hdr = memchr(b'\n', d).map_or(d.len(), |i| i + 1);
        for_recs::<2>(&d[hdr..], |f| {
            prod_raw.push((f[0], f[1].to_vec()));
        });
    }
    for (_, c) in &prod_raw {
        cat_names.push(c.clone());
    }
    cat_names.push(b"unknown".to_vec());
    cat_names.sort();
    cat_names.dedup();
    assert!(cat_names.len() <= 64, "too many categories");
    let unknown_id = cat_names.iter().position(|c| c == b"unknown").unwrap() as u16;
    let mut products: FMap<&'static [u8], u16> = FMap::default();
    for (p, c) in &prod_raw {
        products.insert(p, cat_names.iter().position(|x| x == c).unwrap() as u16);
    }
    // unknown product => NONE_CAT => mapped to unknown_id at the end of stage 2
    let mut camp_names: Vec<(&'static [u8], &'static [u8])> = vec![];
    let mut camps: FMap<&'static [u8], u32> = FMap::default();
    {
        let d = read_small(&data.join("campaigns.csv"));
        let hdr = memchr(b'\n', d).map_or(d.len(), |i| i + 1);
        for_recs::<2>(&d[hdr..], |f| {
            if !camps.contains_key(f[0]) {
                camps.insert(f[0], camp_names.len() as u32);
                camp_names.push((f[0], f[1]));
            }
        });
    }
    let ncamp = camp_names.len();

    let ev_files: Vec<Bytes> = csv_files(&data.join("events")).iter().map(|p| map_file(p)).collect();
    let ck_files: Vec<Bytes> = csv_files(&data.join("clicks")).iter().map(|p| map_file(p)).collect();
    let lk_files: Vec<Bytes> = csv_files(&data.join("links")).iter().map(|p| map_file(p)).collect();
    lap("setup");

    lap("setup");

    // ---- links
    let mut lchunks = vec![];
    make_chunks(&lk_files, 2, &mut lchunks);
    let next = AtomicUsize::new(0);
    let edges: Vec<Vec<(u64, u64, u64, u64)>> = thread::scope(|sc| {
        let hs: Vec<_> = (0..nthreads)
            .map(|_| {
                sc.spawn(|| {
                    let mut v = vec![];
                    loop {
                        let i = next.fetch_add(1, Relaxed);
                        let Some(c) = lchunks.get(i) else { break };
                        for_recs::<2>(&c.file[c.start..c.end], |f| {
                            if f[0].is_empty() || f[1].is_empty() || f[0] == f[1] {
                                return;
                            }
                            v.push((h64(f[0]), mkref(f[0]), h64(f[1]), mkref(f[1])));
                        });
                    }
                    v
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let total_edges: usize = edges.iter().map(|v| v.len()).sum();
    let links = LinkTable::new(total_edges * 3);
    let next = AtomicUsize::new(0);
    thread::scope(|sc| {
        for _ in 0..nthreads {
            sc.spawn(|| loop {
                let i = next.fetch_add(1, Relaxed);
                let Some(v) = edges.get(i) else { break };
                for &(ha, ra, hb, rb) in v.iter() {
                    let a = links.insert(ha, ra);
                    let b = links.insert(hb, rb);
                    links.union(a, b);
                }
            });
        }
    });
    drop(edges);
    {
        let cap = links.s.len();
        let step = 1 << 16;
        let next = AtomicUsize::new(0);
        thread::scope(|sc| {
            for _ in 0..nthreads {
                sc.spawn(|| loop {
                    let i = next.fetch_add(1, Relaxed) * step;
                    if i >= cap {
                        break;
                    }
                    links.flatten_range(i, (i + step).min(cap));
                });
            }
        });
    }
    lap("links");

    let ctx = Ctx { ws, we, base_day, nd, products, camps, ncamp, unknown_id, links, nthreads };

    // ---- stage 1: parse events + clicks
    let mut chunks = vec![];
    make_chunks(&ev_files, 0, &mut chunks);
    make_chunks(&ck_files, 1, &mut chunks);
    let ev_bytes: usize = ev_files.iter().map(|f| f.len()).sum();
    let _ = ev_bytes;
    let pool: &'static Pool = Box::leak(Box::new(Pool::new()));
    let next = AtomicUsize::new(0);
    let w1s: Vec<W1> = thread::scope(|sc| {
        let (chunks, ctx, next) = (&chunks, &ctx, &next);
        let hs: Vec<_> = (0..nthreads)
            .map(|tid| {
                sc.spawn(move || {
                    let mut w = W1 {
                        pe: (0..NBP).map(|_| BW::new()).collect(),
                        dr: (0..NBE).map(|_| BW::new()).collect(),
                        cb: (0..NBP).map(|_| BW::new()).collect(),
                        pool,
                        dc: DCache::new(),
                        wid: tid as u64,
                        ebatch: Vec::with_capacity(64),
                        cbatch: Vec::with_capacity(64),
                    };
                    loop {
                        let i = next.fetch_add(1, Relaxed);
                        let Some(c) = chunks.get(i) else { break };
                        let d = &c.file[c.start..c.end];
                        if c.kind == 0 {
                            for_recs::<7>(d, |f| parse_event(f, ctx, &mut w));
                            flush_events(ctx, &mut w);
                        } else {
                            for_recs::<4>(d, |f| parse_click(f, ctx, &mut w));
                            flush_clicks(ctx, &mut w);
                        }
                    }
                    w
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    lap("stage1 parse");

    // ---- stage 2: dedup -> mark losing copies in per-writer bitmaps
    let mut loff: Vec<Vec<usize>> = Vec::new();
    let mut lose: Vec<Vec<AtomicU64>> = Vec::new();
    for w in &w1s {
        let mut off = Vec::with_capacity(NBP + 1);
        let mut tot = 0usize;
        for pb in 0..NBP {
            off.push(tot);
            tot += (w.pe[pb].n as usize + 63) / 64;
        }
        off.push(tot);
        lose.push((0..tot).map(|_| AtomicU64::new(0)).collect());
        loff.push(off);
    }
    let next = AtomicUsize::new(0);
    thread::scope(|sc| {
        for _ in 0..nthreads {
            sc.spawn(|| {
                let mut table: Vec<(u64, u32, u32)> = Vec::new();
                loop {
                    let b = next.fetch_add(1, Relaxed);
                    if b >= NBE {
                        break;
                    }
                    let total: usize = w1s.iter().map(|w| w.dr[b].len()).sum();
                    let cap = (total * 2).next_power_of_two().max(16);
                    let mask = cap - 1;
                    table.clear();
                    table.resize(cap, (0, 0, 0));
                    let mut flat = 0u32;
                    for w in &w1s {
                        w.dr[b].for_slices(|sl| {
                            for r in sl {
                                let mut i = (r.eid as usize) & mask;
                                loop {
                                    let t = &mut table[i];
                                    if t.0 == r.eid {
                                        if r.ingest < t.1 {
                                            t.1 = r.ingest;
                                            t.2 = flat;
                                        }
                                        break;
                                    }
                                    if t.0 == 0 {
                                        *t = (r.eid, r.ingest, flat);
                                        break;
                                    }
                                    i = (i + 1) & mask;
                                }
                                flat += 1;
                            }
                        });
                    }
                    flat = 0;
                    for w in &w1s {
                        w.dr[b].for_slices(|sl| {
                            for r in sl {
                                let cur = flat;
                                flat += 1;
                                if r.loc == 0 {
                                    continue;
                                }
                                let mut i = (r.eid as usize) & mask;
                                loop {
                                    let t = &table[i];
                                    if t.0 == r.eid {
                                        if t.2 != cur {
                                            let wid = ((r.loc >> 40) & 0xFF) as usize;
                                            let pb = ((r.loc >> 48) & 0xFFF) as usize;
                                            let idx = (r.loc & 0xFF_FFFF_FFFF) as usize;
                                            lose[wid][loff[wid][pb] + (idx >> 6)].fetch_or(1u64 << (idx & 63), Relaxed);
                                        }
                                        break;
                                    }
                                    i = (i + 1) & mask;
                                }
                            }
                        });
                        pool.free_all(&w.dr[b].blocks);
                    }
                }
            });
        }
    });
    lap("stage2 dedup");

    // ---- stage 3: sessions, attribution, user rows
    let out_user = out.join("user_daily");
    let out_camp = out.join("campaign_daily");
    std::fs::create_dir_all(&out_user).expect("mkdir");
    std::fs::create_dir_all(&out_camp).expect("mkdir");
    let next = AtomicUsize::new(0);
    let mut order: Vec<usize> = (0..NBP).collect();
    {
        let sizes: Vec<usize> = (0..NBP)
            .map(|b| w1s.iter().map(|w| (w.pe[b].n + w.cb[b].n) as usize).sum::<usize>())
            .collect();
        order.sort_by_key(|&b| std::cmp::Reverse(sizes[b]));
    }
    let order = &order;
    let cat_names_ref = &cat_names;
    let results: Vec<(Vec<CAcc>, usize)> = thread::scope(|sc| {
        let hs: Vec<_> = (0..nthreads)
            .map(|tid| {
                let (w1s, ctx, next, out_user, order, lose, loff) = (&w1s, &ctx, &next, &out_user, order, &lose, &loff);
                sc.spawn(move || {
                    let mut st = S3 {
                        ur: URows { nref: vec![], day: vec![], sessions: vec![], events: vec![], rev: vec![], top: vec![] },
                        acc: vec![CAcc::default(); (ctx.ncamp + 1) * ctx.nd],
                        ev: vec![],
                        ck: vec![],
                        starts: vec![],
                        days: vec![],
                        srev: vec![],
                        runs: vec![],
                        cs: vec![],
                        catacc: vec![],
                    };
                    loop {
                        let oi = next.fetch_add(1, Relaxed);
                        if oi >= NBP {
                            break;
                        }
                        let b = order[oi];
                        let mut ev = std::mem::take(&mut st.ev);
                        let mut ck = std::mem::take(&mut st.ck);
                        ev.clear();
                        ck.clear();
                        for (wid, w) in w1s.iter().enumerate() {
                            let words = &lose[wid][loff[wid][b]..];
                            let mut idx = 0usize;
                            w.pe[b].for_slices(|sl| {
                                for r in sl {
                                    if (words[idx >> 6].load(Relaxed) >> (idx & 63)) & 1 == 0 {
                                        ev.push(*r);
                                    }
                                    idx += 1;
                                }
                            });
                        }
                        for w in w1s.iter() {
                            w.cb[b].for_slices(|sl| ck.extend_from_slice(sl));
                        }
                        ev.sort_unstable_by(|a, b| (a.pkey, a.packed).cmp(&(b.pkey, b.packed)));
                        ck.sort_unstable_by(|a, b| (a.pkey, a.tc).cmp(&(b.pkey, b.tc)));
                        let (mut i, mut c) = (0usize, 0usize);
                        while i < ev.len() {
                            let pk = ev[i].pkey;
                            let mut j = i + 1;
                            while j < ev.len() && ev[j].pkey == pk {
                                j += 1;
                            }
                            while c < ck.len() && ck[c].pkey < pk {
                                c += 1;
                            }
                            let mut ce = c;
                            while ce < ck.len() && ck[ce].pkey == pk {
                                ce += 1;
                            }
                            process_person(&ev[i..j], &ck[c..ce], ctx, &mut st);
                            c = ce;
                            i = j;
                        }
                        st.ev = ev;
                        st.ck = ck;
                    }
                    // write user parquet
                    let n = st.ur.nref.len();
                    if n > 0 {
                        let names: Vec<&[u8]> = st.ur.nref.iter().map(|&r| deref(r)).collect();
                        let tops: Vec<Option<&[u8]>> = st
                            .ur
                            .top
                            .iter()
                            .map(|&t| if t == NONE_CAT { None } else { Some(&cat_names_ref[t as usize][..]) })
                            .collect();
                        let mut w = pq::Writer::new(user_fields());
                        let rg = 1 << 20;
                        let mut s = 0;
                        while s < n {
                            let e = (s + rg).min(n);
                            w.row_group(
                                &[
                                    pq::Col::Str(&names[s..e]),
                                    pq::Col::I32(&st.ur.day[s..e]),
                                    pq::Col::I32(&st.ur.sessions[s..e]),
                                    pq::Col::I32(&st.ur.events[s..e]),
                                    pq::Col::I64(&st.ur.rev[s..e]),
                                    pq::Col::OptStr(&tops[s..e]),
                                ],
                                e - s,
                            );
                            s = e;
                        }
                        write_file(&out_user.join(format!("part-{tid:03}.parquet")), &w.finish());
                    }
                    (st.acc, n)
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    lap("stage3");

    let total_user_rows: usize = results.iter().map(|r| r.1).sum();
    if total_user_rows == 0 {
        let w = pq::Writer::new(user_fields());
        write_file(&out_user.join("part-000.parquet"), &w.finish());
    }

    // campaign table
    let mut acc = vec![CAcc::default(); (ncamp + 1) * nd];
    for (a, _) in &results {
        for (x, y) in acc.iter_mut().zip(a) {
            x.sessions += y.sessions;
            x.purch += y.purch;
            x.assisted += y.assisted;
            x.rev += y.rev;
        }
    }
    let mut cid: Vec<&[u8]> = vec![];
    let mut chn: Vec<&[u8]> = vec![];
    let mut cday: Vec<i32> = vec![];
    let (mut c1, mut c2, mut c3, mut c4) = (vec![], vec![], vec![], vec![]);
    for c in 0..=ncamp {
        for d in 0..nd {
            let a = &acc[c * nd + d];
            if a.sessions == 0 && a.assisted == 0 {
                continue;
            }
            let (id, ch): (&[u8], &[u8]) = if c == ncamp { (b"organic", b"organic") } else { camp_names[c] };
            cid.push(id);
            chn.push(ch);
            cday.push((base_day + d as i64) as i32);
            c1.push(a.sessions as i32);
            c2.push(a.purch as i32);
            c3.push(a.rev as i64);
            c4.push(a.assisted as i32);
        }
    }
    let mut w = pq::Writer::new(camp_fields());
    if !cid.is_empty() {
        w.row_group(
            &[
                pq::Col::Str(&cid),
                pq::Col::Str(&chn),
                pq::Col::I32(&cday),
                pq::Col::I32(&c1),
                pq::Col::I32(&c2),
                pq::Col::I64(&c3),
                pq::Col::I32(&c4),
            ],
            cid.len(),
        );
    }
    write_file(&out_camp.join("part-000.parquet"), &w.finish());
    lap("done");
    std::process::exit(0);
}

fn user_fields() -> Vec<pq::Field> {
    use pq::Kind::*;
    vec![
        pq::Field { name: "user_id", kind: Str },
        pq::Field { name: "day", kind: Date },
        pq::Field { name: "sessions", kind: I32 },
        pq::Field { name: "events", kind: I32 },
        pq::Field { name: "revenue_cents", kind: I64 },
        pq::Field { name: "top_category", kind: OptStr },
    ]
}
fn camp_fields() -> Vec<pq::Field> {
    use pq::Kind::*;
    vec![
        pq::Field { name: "campaign_id", kind: Str },
        pq::Field { name: "channel", kind: Str },
        pq::Field { name: "day", kind: Date },
        pq::Field { name: "sessions", kind: I32 },
        pq::Field { name: "purchasing_sessions", kind: I32 },
        pq::Field { name: "revenue_cents", kind: I64 },
        pq::Field { name: "assisted_sessions", kind: I32 },
    ]
}
