mod pq;

use memchr::memchr;
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
const NBE: usize = 1024;
const NBP: usize = 1024;
const CHUNK: usize = 4 << 20;
const NONE_CAT: u16 = u16::MAX;

type Bytes = &'static [u8];

/// 64-bit ID hash. IDs of up to 16 bytes (all of them in practice) take an inline
/// multiply-fold path that reads 16 bytes; every input buffer is padded so this stays mapped.
#[inline(always)]
fn h64(b: &[u8]) -> u64 {
    let n = b.len();
    let h = if n <= 16 && n > 0 {
        let p = b.as_ptr();
        // bzhi keeps the low `index` bits (all of them when index >= 64)
        let (lo, hi) = unsafe {
            (
                _bzhi_u64((p as *const u64).read_unaligned(), (8 * n) as u32),
                _bzhi_u64((p.add(8) as *const u64).read_unaligned(), (8 * n).saturating_sub(64) as u32),
            )
        };
        let m = ((lo ^ 0x9E37_79B9_7F4A_7C15) as u128) * ((hi ^ 0xC2B2_AE3D_27D4_EB4F ^ (n as u64)) as u128);
        let mut h = (m as u64) ^ ((m >> 64) as u64);
        h = (h ^ (h >> 29)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        h ^ (h >> 32)
    } else {
        xxh3_64(b)
    };
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

#[inline(always)]
unsafe fn flatten8(out: *mut u32, mut m: u64, base: u32) -> usize {
    let cnt = m.count_ones() as usize;
    let mut i = 0;
    loop {
        for k in 0..8 {
            *out.add(i + k) = base + m.trailing_zeros();
            m &= m.wrapping_sub(1);
        }
        i += 8;
        if i >= cnt {
            break;
        }
    }
    cnt
}

const WB: usize = 64; // 64-byte blocks per scan window

/// Structural CSV scanner. Calls `f` with the N fields of every well-formed record (quotes
/// stripped); malformed records (wrong field count, stray quotes, empty lines) are skipped.
#[inline(always)]
unsafe fn drive<const AVX: bool, const N: usize, F: FnMut(&[&'static [u8]; N])>(d: &'static [u8], f: &mut F) {
    let n = d.len();
    assert!(n < (1usize << 31));
    let dp = d.as_ptr();
    let mut pos = [0u32; WB * 64 + 128];
    let mut nlp = [0u32; WB * 64 + 16];
    let mut nlq = [0u32; WB * 64 + 16];
    let mut fields: [&'static [u8]; N] = [&[]; N];
    let mut tail = [0u8; 64];
    let (mut np, mut ip) = (0usize, 0usize);
    let mut base = 0usize;
    let mut qcum = 0u32;
    let mut lstart = 0u32;
    let mut qstart = 0u32;
    loop {
        let mut nn = 0usize;
        let mut blocks = 0;
        while base < n && blocks < WB {
            let p = if base + 64 <= n {
                dp.add(base)
            } else {
                let r = n - base;
                tail = [0u8; 64];
                tail[..r].copy_from_slice(&d[base..]);
                tail.as_ptr()
            };
            let (mn, mc, mq) = masks::<AVX>(p);
            np += flatten8(pos.as_mut_ptr().add(np), mn | mc, base as u32);
            let mut m = mn;
            while m != 0 {
                let b = m.trailing_zeros();
                *nlp.get_unchecked_mut(nn) = base as u32 + b;
                *nlq.get_unchecked_mut(nn) = qcum + (mq & ((1u64 << b) - 1)).count_ones();
                nn += 1;
                m &= m - 1;
            }
            qcum += mq.count_ones();
            base += 64;
            blocks += 1;
        }
        let done = base >= n;
        if done && (lstart as usize) < n {
            // last record without a trailing newline
            *pos.get_unchecked_mut(np) = n as u32;
            np += 1;
            *nlp.get_unchecked_mut(nn) = n as u32;
            *nlq.get_unchecked_mut(nn) = qcum;
            nn += 1;
        }
        for li in 0..nn {
            let e = *nlp.get_unchecked(li);
            let qe = *nlq.get_unchecked(li);
            if ip + N - 1 < np && *pos.get_unchecked(ip + N - 1) == e {
                let mut st = lstart as usize;
                let mut qf = 0u32;
                for k in 0..N {
                    let en = *pos.get_unchecked(ip + k) as usize;
                    let len = en - st;
                    // inputs are padded / preceded by a header, so these reads stay mapped
                    let c0 = *dp.add(st);
                    let c1 = *dp.wrapping_add(en).wrapping_sub(1);
                    let q = ((len >= 2) & (c0 == b'"') & (c1 == b'"')) as usize;
                    qf += q as u32;
                    *fields.get_unchecked_mut(k) = std::slice::from_raw_parts(dp.add(st + q), len - 2 * q);
                    st = en + 1;
                }
                if qe - qstart == 2 * qf {
                    f(&fields);
                }
                ip += N;
            } else {
                while *pos.get_unchecked(ip) != e {
                    ip += 1;
                }
                ip += 1;
            }
            lstart = e + 1;
            qstart = qe;
        }
        if done {
            break;
        }
        // carry the delimiters of the unfinished record; more than N of them means it is malformed anyway
        let rem = (np - ip).min(N);
        std::ptr::copy(pos.as_ptr().add(ip), pos.as_mut_ptr(), rem);
        np = rem;
        ip = 0;
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
fn ld8(f: &[u8], i: usize) -> u64 {
    debug_assert!(i + 8 <= f.len());
    unsafe { (f.as_ptr().add(i) as *const u64).read_unaligned() }
}
const POW10: [u64; 9] = [1, 10, 100, 1000, 10_000, 100_000, 1_000_000, 10_000_000, 100_000_000];
#[inline(always)]
fn parse_ms(f: &[u8]) -> Option<i64> {
    let n = f.len();
    if n >= 9 && n <= 16 {
        let a = parse8(ld8(f, 0))?;
        let k = 16 - n; // leading bytes of the second load that overlap the first
        let m = (1u64 << (8 * k)).wrapping_sub(1);
        let t = (ld8(f, n - 8) & !m) | (0x3030_3030_3030_3030 & m);
        let b = parse8(t)?;
        return Some((a * POW10[n - 8] + b) as i64);
    }
    if n == 0 {
        return None;
    }
    if n <= 18 {
        let mut acc: u64 = 0;
        let mut i = 0;
        if n >= 8 {
            acc = parse8(ld8(f, 0))?;
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
    if (n == 20 || n == 25) && unsafe { *f.get_unchecked(4) } == b'-' {
        parse_iso(f, c)
    } else {
        parse_ms(f)
    }
}
/// `ingest_ts` is always valid F1 (rules); take the lean path for that shape.
#[inline(always)]
/// Returns (milliseconds, whole seconds floored).
fn parse_ingest(f: &[u8], c: &mut DCache) -> Option<(i64, i64)> {
    let slow = |f: &[u8], c: &mut DCache| parse_ts(f, c).map(|ms| (ms, if ms >= 0 { ms / 1000 } else { -1 }));
    if f.len() != 20 {
        return slow(f, c);
    }
    let k1 = ld8(f, 0);
    let k2 = u16::from_le_bytes([unsafe { *f.get_unchecked(8) }, unsafe { *f.get_unchecked(9) }]);
    let idx = ((k1 ^ ((k2 as u64) << 3)).wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 57) as usize;
    if c.k1[idx] != k1 || c.k2[idx] != k2 {
        return slow(f, c);
    }
    let t = ld8(f, 11) ^ 0x3030_3A30_303A_3030;
    let u = t.wrapping_mul(10).wrapping_add(t >> 8);
    let secs = (u & 0xFF) as i64 * 3600 + ((u >> 24) & 0xFF) as i64 * 60 + ((u >> 48) & 0xFF) as i64;
    let sec = c.days[idx] * 86_400 + secs;
    Some((sec * 1000, sec))
}

/// F1 `YYYY-MM-DDTHH:MM:SSZ` or F2 `YYYY-MM-DDTHH:MM:SS+HH:MM` (caller checked length 20/25).
#[inline(always)]
fn parse_iso(f: &[u8], c: &mut DCache) -> Option<i64> {
    let n = f.len();
    const HI: u64 = 0x8080_8080_8080_8080;
    // HH:MM:SS in one load: xor with the template "00:00:00"; digits become 0..9, colons 0
    let t = ld8(f, 11) ^ 0x3030_3A30_303A_3030;
    let mut bad = ((t.wrapping_add(0x7676_7676_7676_7676) | t) & HI) | (t & 0x0000_FF00_00FF_0000);
    let u = t.wrapping_mul(10).wrapping_add(t >> 8);
    let (h, mi, sec) = ((u & 0xFF) as i64, ((u >> 24) & 0xFF) as i64, ((u >> 48) & 0xFF) as i64);
    let at = |i: usize| unsafe { *f.get_unchecked(i) };
    bad |= (at(10) != b'T') as u64 | (h > 23) as u64 | (mi > 59) as u64 | (sec > 59) as u64;
    let mut off = 0i64;
    if n == 20 {
        bad |= (at(19) != b'Z') as u64;
    } else {
        // bytes 17..25 = "SS+HH:MM"; check/parse bytes 3..7
        let y = ld8(f, 17);
        let t2 = (y ^ 0x3030_3A30_3000_0000) & 0xFFFF_FFFF_FF00_0000;
        bad |= ((t2.wrapping_add(0x7676_7676_7600_0000) | t2) & HI) | (t2 & 0x0000_FF00_0000_0000);
        let u2 = t2.wrapping_mul(10).wrapping_add(t2 >> 8);
        let (oh, om) = (((u2 >> 24) & 0xFF) as i64, ((u2 >> 48) & 0xFF) as i64);
        let sg = at(19);
        bad |= (oh > 23) as u64 | (om > 59) as u64 | ((sg != b'+') & (sg != b'-')) as u64;
        let mag = (oh * 60 + om) * 60_000;
        off = if sg == b'-' { -mag } else { mag };
    }
    if bad != 0 {
        return None;
    }
    let k1 = ld8(f, 0);
    let k2 = u16::from_le_bytes([at(8), at(9)]);
    let idx = ((k1 ^ ((k2 as u64) << 3)).wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 57) as usize;
    let days = if c.k1[idx] == k1 && c.k2[idx] == k2 {
        c.days[idx]
    } else {
        let days = parse_date(f)?;
        c.k1[idx] = k1;
        c.k2[idx] = k2;
        c.days[idx] = days;
        days
    };
    Some((days * 86_400 + h * 3600 + mi * 60 + sec) * 1000 - off)
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

/// Map a file read-only with at least 4 KB of zero padding after its end, so parsers may
/// over-read a few bytes past the last field.
fn map_file(p: &Path) -> Bytes {
    use std::os::unix::io::AsRawFd;
    let f = std::fs::File::open(p).expect("open");
    let len = f.metadata().map(|m| m.len()).unwrap_or(0) as usize;
    if len == 0 {
        return &[];
    }
    unsafe {
        let pg = 4096usize;
        let total = (len + pg - 1) / pg * pg + pg;
        let base = libc::mmap(
            std::ptr::null_mut(),
            total,
            libc::PROT_READ,
            libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE,
            -1,
            0,
        );
        assert!(base != libc::MAP_FAILED, "mmap reserve");
        let m = libc::mmap(base, len, libc::PROT_READ, libc::MAP_PRIVATE | libc::MAP_FIXED, f.as_raw_fd(), 0);
        assert!(m == base, "mmap file");
        std::slice::from_raw_parts(base as *const u8, len)
    }
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
    let mut v = std::fs::read(p).unwrap_or_default();
    let n = v.len();
    v.extend_from_slice(&[0u8; 64]); // padding for over-reads
    &Box::leak(v.into_boxed_slice())[..n]
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
    /// Returns (slot, newly inserted).
    fn insert(&self, h: u64, rf: u64) -> (usize, bool) {
        let mut i = (h as usize) & self.mask;
        loop {
            let k = self.s[i].key.load(Acquire);
            if k == h {
                return (i, false);
            }
            if k == 0 {
                if self.s[i].key.compare_exchange(0, RESERVED, AcqRel, Acquire).is_ok() {
                    self.s[i].rf.store(rf, Relaxed);
                    self.s[i].pre.store(prefix8(deref(rf)), Relaxed);
                    self.s[i].key.store(h, Release);
                    return (i, true);
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
    /// Resolve every id to its root and record id -> root name in the person map.
    fn flatten_range(&self, lo: usize, hi: usize, pm: &PersonMap) {
        for i in lo..hi {
            let k = self.s[i].key.load(Relaxed);
            if k == 0 {
                continue;
            }
            let r = self.find(i);
            pm.insert(k, self.s[r].rf.load(Relaxed));
        }
    }
}

/// Compact read-only map built after union-find: user id hash -> name ref of its person's root.
/// 16-byte slots at <= 50% load, so it is a quarter of the size of the union-find table.
struct PersonMap {
    s: Box<[(AtomicU64, AtomicU64)]>,
    mask: usize,
}
impl PersonMap {
    fn new(n: usize) -> Self {
        let cap = (n * 2).next_power_of_two().max(16);
        let s = unsafe {
            let p = map_zero(cap * 16) as *mut (AtomicU64, AtomicU64);
            Box::from_raw(std::slice::from_raw_parts_mut(p, cap))
        };
        PersonMap { s, mask: cap - 1 }
    }
    /// Keys are distinct; concurrent inserts are fine (readers start after a join).
    fn insert(&self, k: u64, rf: u64) {
        let mut i = (k as usize) & self.mask;
        loop {
            if self.s[i].0.compare_exchange(0, k, Relaxed, Relaxed).is_ok() {
                self.s[i].1.store(rf, Relaxed);
                return;
            }
            i = (i + 1) & self.mask;
        }
    }
    #[inline(always)]
    fn lookup(&self, h: u64) -> Option<u64> {
        let mut i = (h as usize) & self.mask;
        loop {
            let sl = unsafe { self.s.get_unchecked(i) };
            let k = sl.0.load(Relaxed);
            if k == h {
                return Some(sl.1.load(Relaxed));
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
}
/// Person key of a linked person: derived from its root's (canonical) name pointer.
#[inline(always)]
fn pkey_of_root(rf: u64) -> u64 {
    let z = rf.wrapping_mul(0x9E37_79B9_7F4A_7C15);
    z ^ (z >> 29)
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

/// Block writer for 16- or 24-byte records with software write-combining: 8 records are staged
/// in a cache-resident buffer (2 or 3 cache lines) and flushed to the block with non-temporal stores.
#[repr(C, align(64))]
struct BW<T> {
    buf: [T; 8],
    cur: *mut T,
    end: *mut T,
    n: u64,
    blocks: Vec<usize>,
}
unsafe impl<T> Send for BW<T> {}
unsafe impl<T> Sync for BW<T> {}
impl<T: Copy> BW<T> {
    const PER: usize = (BLK / (8 * std::mem::size_of::<T>())) * 8;
    const LINES32: usize = std::mem::size_of::<T>() / 4; // 32-byte stores per flush of 8 records
    fn new() -> Self {
        assert!(std::mem::size_of::<T>() == 24 || std::mem::size_of::<T>() == 16);
        BW { buf: unsafe { std::mem::zeroed() }, cur: std::ptr::null_mut(), end: std::ptr::null_mut(), n: 0, blocks: Vec::new() }
    }
    #[inline(always)]
    fn push(&mut self, v: T, pool: &Pool) {
        unsafe {
            *self.buf.get_unchecked_mut((self.n & 7) as usize) = v;
        }
        self.n += 1;
        if self.n & 7 == 0 {
            self.flush_line(pool);
        }
    }
    #[inline(always)]
    fn flush_line(&mut self, pool: &Pool) {
        if self.cur == self.end {
            self.grow(pool);
        }
        unsafe {
            let s = self.buf.as_ptr() as *const __m256i;
            let d = self.cur as *mut __m256i;
            for i in 0..Self::LINES32 {
                _mm256_stream_si256(d.add(i), _mm256_load_si256(s.add(i)));
            }
            self.cur = self.cur.add(8);
        }
    }
    #[cold]
    #[inline(never)]
    fn grow(&mut self, pool: &Pool) {
        let b = pool.alloc() as *mut T;
        self.blocks.push(b as usize);
        self.cur = b;
        self.end = unsafe { b.add(Self::PER) };
    }
    /// Write out the staged tail (normal stores). Call once when done pushing.
    fn finish(&mut self, pool: &Pool) {
        let k = (self.n & 7) as usize;
        if k > 0 {
            if self.cur == self.end {
                self.grow(pool);
            }
            unsafe {
                std::ptr::copy_nonoverlapping(self.buf.as_ptr(), self.cur, k);
                self.cur = self.cur.add(k);
            }
        }
    }
    fn len(&self) -> usize {
        self.n as usize
    }
    fn for_slices(&self, mut f: impl FnMut(&[T])) {
        let mut left = self.n as usize;
        for &b in self.blocks.iter() {
            let m = left.min(Self::PER);
            f(unsafe { std::slice::from_raw_parts(b as *const T, m) });
            left -= m;
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
/// Dedup record (16 bytes): one per parsed event line. loc = NOLOC for an invalid copy, else
/// pbucket << 22 | index of its PEv in this worker's writer for that bucket (the worker is
/// implied by which worker's dedup blocks the record sits in).
#[derive(Clone, Copy)]
#[repr(C)]
struct DR {
    eid: u64,
    ingest: u32,
    loc: u32,
}
const NOLOC: u32 = u32::MAX;
const IDX_BITS: u32 = 22;
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
    links: PersonMap,
    cnum: Vec<u32>,
    cname: Vec<&'static [u8]>,
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
    let ing = parse_ingest(f[3], &mut w.dc);
    let ingest = match ing {
        Some((_, sec)) if sec >= 0 => sec.min(u32::MAX as i64 - 1) as u32,
        _ => u32::MAX,
    };
    let ing_ms = ing.map(|x| x.0);
    'v: {
        let uidb = f[1];
        if uidb.is_empty() {
            break 'v;
        }
        let Some(ts) = parse_ts(f[2], &mut w.dc) else { break 'v };
        if ts < ctx.ws || ts >= ctx.we {
            break 'v;
        }
        let ty = f[4];
        let kind = if ty.len() == 4 {
            let x = u32::from_le_bytes(unsafe { (ty.as_ptr() as *const [u8; 4]).read_unaligned() });
            if x == u32::from_le_bytes(*b"view") {
                0u64
            } else if x == u32::from_le_bytes(*b"cart") {
                1
            } else {
                break 'v;
            }
        } else if ty.len() == 8 && ld8(ty, 0) == u64::from_le_bytes(*b"purchase") {
            2
        } else {
            break 'v;
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
    w.dr[ebucket(eid)].push(DR { eid, loc: NOLOC, ingest }, w.pool);
}

#[inline(never)]
fn flush_events(ctx: &Ctx, w: &mut W1) {
    let mut b = std::mem::take(&mut w.ebatch);
    for t in b.iter() {
        let (pkey, nref) = match ctx.links.lookup(t.uh) {
            Some(rf) => (pkey_of_root(rf), rf),
            None => (t.uh, t.uref),
        };
        let pb = pbucket(pkey);
        let idx = w.pe[pb].n;
        if idx >= (1u64 << IDX_BITS) - 1 {
            panic!("person bucket too large for compact dedup index");
        }
        w.pe[pb].push(PEv { pkey, nref, packed: t.packed }, w.pool);
        let loc = ((pb as u32) << IDX_BITS) | idx as u32;
        w.dr[ebucket(t.eid)].push(DR { eid: t.eid, loc, ingest: t.ingest }, w.pool);
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
    let Some(camp) = camp_lookup(ctx, f[2]) else { return };
    let uh = h64(f[1]);
    ctx.links.prefetch(uh);
    let tc = (((ts - (ctx.ws - WEEK)) as u64) << 32) | camp as u64;
    w.cbatch.push((uh, mkref(f[0]), tc));
    if w.cbatch.len() >= 32 {
        flush_clicks(ctx, w);
    }
}

/// Campaign id -> index. Ids of the form `c_<digits>` go through a direct table (exact bytes
/// re-checked); anything else uses the hash map.
#[inline(always)]
fn camp_lookup(ctx: &Ctx, f: &[u8]) -> Option<u32> {
    let n = f.len();
    if n >= 3 && n <= 9 && f[0] == b'c' && f[1] == b'_' {
        let mut v = 0usize;
        let mut ok = true;
        for &b in &f[2..] {
            let d = b.wrapping_sub(b'0');
            ok &= d <= 9;
            v = v * 10 + d as usize;
        }
        if ok && v < ctx.cnum.len() {
            let i = ctx.cnum[v];
            if i != u32::MAX && ctx.cname[i as usize] == f {
                return Some(i);
            }
        }
    }
    ctx.camps.get(f).copied()
}

#[inline(never)]
fn flush_clicks(ctx: &Ctx, w: &mut W1) {
    let mut b = std::mem::take(&mut w.cbatch);
    for &(uh, idref, tc) in b.iter() {
        let pkey = match ctx.links.lookup(uh) {
            Some(rf) => pkey_of_root(rf),
            None => uh,
        };
        w.cb[pbucket(pkey)].push(CRec { pkey, idref, tc }, w.pool);
    }
    b.clear();
    w.cbatch = b;
}

// ---------------------------------------------------------------- stage 3 sorting
/// Sort one person's packed events (timestamp in the high 32 bits).
fn sort_u64(g: &mut [u64]) {
    let n = g.len();
    if n <= 3 {
        for i in 1..n {
            let v = g[i];
            let mut j = i;
            while j > 0 && g[j - 1] > v {
                g[j] = g[j - 1];
                j -= 1;
            }
            g[j] = v;
        }
    } else {
        g.sort_unstable();
    }
}

/// Number of elements < t in a sorted non-empty slice (branchless binary search).
#[inline(always)]
fn count_lt(a: &[i64], t: i64) -> usize {
    let mut base = 0usize;
    let mut size = a.len();
    while size > 1 {
        let half = size / 2;
        let mid = base + half;
        base = if unsafe { *a.get_unchecked(mid) } < t { mid } else { base };
        size -= half;
    }
    base + (unsafe { *a.get_unchecked(base) } < t) as usize
}

#[inline(always)]
fn lowmask(k: u32) -> u64 {
    if k >= 64 {
        u64::MAX
    } else {
        (1u64 << k) - 1
    }
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
    ckey: Vec<u64>,
    catacc: Vec<(u16, u64)>,
    last: Vec<u32>,
    sid: u32,
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

fn process_person(name: u64, evs: &[u64], cks: &[CRec], ctx: &Ctx, st: &mut S3) {
    let nd = ctx.nd;
    let organic = ctx.ncamp;
    st.starts.clear();
    st.days.clear();
    st.srev.clear();
    st.runs.clear();
    st.catacc.clear();
    let mut prev = 0i64;
    let mut cur_day: i64 = -1;
    let (mut us, mut ue, mut ur) = (0u32, 0u32, 0u64);
    for &packed in evs {
        let ets = ctx.ws + (packed >> 32) as i64;
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
        if (packed >> 24) & 3 == 2 {
            let p = packed & 0xFF_FFFF;
            let cat = ((packed >> 26) & 63) as u16;
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
    // assists for light persons: each session's 7-day click window is exactly [lo, hi), so count
    // its distinct campaigns there (stamp = per-thread session id); heavy persons use intervals below
    let window = n * cks.len() <= 4096;
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
        let day = st.days[s] as usize;
        let a = &mut st.acc[camp * nd + day];
        a.sessions += 1;
        let r = st.srev[s];
        if r > 0 {
            a.purch += 1;
            a.rev += r;
        }
        if window && hi > lo {
            st.sid = st.sid.wrapping_add(1);
            let sid = st.sid;
            for k in lo..hi {
                let c = (cks[k].tc as u32) as usize;
                let l = unsafe { st.last.get_unchecked_mut(c) };
                if *l != sid {
                    *l = sid;
                    st.acc[c * nd + day].assisted += 1;
                }
            }
        }
    }
    // assists: per campaign, the union over its clicks of the sessions starting in [t, t + 7 days]
    if !window && !cks.is_empty() {
        st.ckey.clear();
        for c in cks {
            st.ckey.push(((c.tc as u32 as u64) << 32) | (c.tc >> 32));
        }
        st.ckey.sort_unstable();
        let first = st.starts[0];
        let last = st.starts[n - 1];
        let nrun = st.runs.len();
        let small = n <= 64;
        let mut rmask = [0u64; 64];
        if small {
            for r in 0..nrun {
                let lo = st.runs[r].1 as u32;
                let hi = if r + 1 < nrun { st.runs[r + 1].1 as u32 } else { n as u32 };
                rmask[r] = lowmask(hi) & !lowmask(lo);
            }
        }
        let mut i0 = 0;
        let nk = st.ckey.len();
        while i0 < nk {
            let camp = (st.ckey[i0] >> 32) as usize;
            let mut i1 = i0 + 1;
            while i1 < nk && (st.ckey[i1] >> 32) as usize == camp {
                i1 += 1;
            }
            if small {
                let mut m = 0u64;
                for k in i0..i1 {
                    let t = cbase + (st.ckey[k] & 0xFFFF_FFFF) as i64;
                    if t > last || t + WEEK < first {
                        continue;
                    }
                    let (i, j) = if n <= 16 {
                        let (mut i, mut j) = (0u32, 0u32);
                        for &s0 in &st.starts {
                            i += (s0 < t) as u32;
                            j += (s0 <= t + WEEK) as u32;
                        }
                        (i, j)
                    } else {
                        (count_lt(&st.starts, t) as u32, count_lt(&st.starts, t + WEEK + 1) as u32)
                    };
                    m |= lowmask(j) & !lowmask(i);
                }
                if m != 0 {
                    for r in 0..nrun {
                        let c = (m & rmask[r]).count_ones();
                        if c > 0 {
                            st.acc[camp * nd + st.runs[r].0 as usize].assisted += c;
                        }
                    }
                }
            } else {
                let mut end = 0usize;
                for k in i0..i1 {
                    let t = cbase + (st.ckey[k] & 0xFFFF_FFFF) as i64;
                    if t > last || t + WEEK < first {
                        continue;
                    }
                    let i = st.starts.partition_point(|&s| s < t);
                    let j = st.starts.partition_point(|&s| s <= t + WEEK);
                    let x = i.max(end);
                    if j > x {
                        // add range [x, j), split by day runs
                        let mut r = st.runs.partition_point(|r| (r.1 as usize) <= x) - 1;
                        let mut pos = x;
                        while pos < j {
                            let seg_end = if r + 1 < nrun { st.runs[r + 1].1 as usize } else { n };
                            let take = seg_end.min(j) - pos;
                            st.acc[camp * nd + st.runs[r].0 as usize].assisted += take as u32;
                            pos += take;
                            r += 1;
                        }
                        end = j;
                    }
                }
            }
            i0 = i1;
        }
    }
}

struct Dims {
    cat_names: Vec<Vec<u8>>,
    unknown_id: u16,
    products: FMap<&'static [u8], u16>,
    camp_names: Vec<(&'static [u8], &'static [u8])>,
    camps: FMap<&'static [u8], u32>,
}

fn load_dims(data: &Path) -> Dims {
    let mut prod_raw: Vec<(&'static [u8], &'static [u8])> = vec![];
    {
        let d = read_small(&data.join("products.csv"));
        let hdr = memchr(b'\n', d).map_or(d.len(), |i| i + 1);
        for_recs::<2>(&d[hdr..], |f| prod_raw.push((f[0], f[1])));
    }
    let mut cat_set: FMap<&'static [u8], u16> = FMap::default();
    for (_, c) in &prod_raw {
        cat_set.insert(c, 0);
    }
    let mut cat_names: Vec<Vec<u8>> = cat_set.keys().map(|c| c.to_vec()).collect();
    if !cat_names.iter().any(|c| c == b"unknown") {
        cat_names.push(b"unknown".to_vec());
    }
    cat_names.sort();
    assert!(cat_names.len() <= 64, "too many categories");
    for (i, c) in cat_names.iter().enumerate() {
        if let Some(v) = cat_set.get_mut(&c[..]) {
            *v = i as u16;
        }
    }
    let unknown_id = cat_names.iter().position(|c| c == b"unknown").unwrap() as u16;
    let mut products: FMap<&'static [u8], u16> = FMap::default();
    products.reserve(prod_raw.len());
    for (p, c) in &prod_raw {
        products.insert(p, cat_set[c]);
    }
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
    Dims { cat_names, unknown_id, products, camp_names, camps }
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

    // products / campaigns: loaded on a side thread while links are processed
    let dims_h = {
        let d = data.clone();
        thread::spawn(move || load_dims(&d))
    };

    let ev_files: Vec<Bytes> = csv_files(&data.join("events")).iter().map(|p| map_file(p)).collect();
    let ck_files: Vec<Bytes> = csv_files(&data.join("clicks")).iter().map(|p| map_file(p)).collect();
    let lk_files: Vec<Bytes> = csv_files(&data.join("links")).iter().map(|p| map_file(p)).collect();
    // ask the kernel to read ahead everything we will scan (a no-op if the files are cached; with a
    // cold cache this keeps many reads in flight instead of one page-fault readahead per thread)
    {
        let all: Vec<Bytes> = lk_files.iter().chain(ev_files.iter()).chain(ck_files.iter()).copied().collect();
        thread::spawn(move || {
            // only for ranges not already in the page cache (mincore is cheap; WILLNEED on cached
            // pages still costs ~1us per page)
            const STEP: usize = 4 << 20;
            let mut vec = vec![0u8; STEP / 4096 + 1];
            for d in all {
                let mut off = 0;
                while off < d.len() {
                    let len = STEP.min(d.len() - off);
                    let p = unsafe { d.as_ptr().add(off) };
                    let r = unsafe { libc::mincore(p as *mut libc::c_void, len, vec.as_mut_ptr()) };
                    let pages = (len + 4095) / 4096;
                    if r != 0 || vec[..pages].iter().any(|&b| b & 1 == 0) {
                        unsafe { libc::madvise(p as *mut libc::c_void, len, libc::MADV_WILLNEED) };
                    }
                    off += len;
                }
            }
        });
    }
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
    let links = LinkTable::new(total_edges * 2 + 16);
    let next = AtomicUsize::new(0);
    let nkeys = AtomicUsize::new(0);
    thread::scope(|sc| {
        for _ in 0..nthreads {
            sc.spawn(|| {
                let mut nk = 0usize;
                loop {
                    let i = next.fetch_add(1, Relaxed);
                    let Some(v) = edges.get(i) else { break };
                    for &(ha, ra, hb, rb) in v.iter() {
                        let (a, na) = links.insert(ha, ra);
                        let (b, nb) = links.insert(hb, rb);
                        nk += na as usize + nb as usize;
                        links.union(a, b);
                    }
                }
                nkeys.fetch_add(nk, Relaxed);
            });
        }
    });
    let pmap = PersonMap::new(nkeys.load(Relaxed));
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
                    links.flatten_range(i, (i + step).min(cap), &pmap);
                });
            }
        });
    }
    lap("links");

    let Dims { cat_names, unknown_id, products, camp_names, camps } = dims_h.join().unwrap();
    let ncamp = camp_names.len();
    let mut cnum: Vec<u32> = Vec::new();
    for (i, (id, _)) in camp_names.iter().enumerate() {
        if id.len() >= 3 && id.len() <= 9 && id.starts_with(b"c_") && id[2..].iter().all(|b| b.is_ascii_digit()) {
            let v: usize = std::str::from_utf8(&id[2..]).unwrap().parse().unwrap();
            if v < 1 << 20 {
                if cnum.len() <= v {
                    cnum.resize(v + 1, u32::MAX);
                }
                if cnum[v] == u32::MAX {
                    cnum[v] = i as u32;
                }
            }
        }
    }
    let cname: Vec<&'static [u8]> = camp_names.iter().map(|c| c.0).collect();
    let ctx = Ctx { ws, we, base_day, nd, products, camps, ncamp, unknown_id, links: pmap, cnum, cname, nthreads };

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
                    for x in w.pe.iter_mut() { x.finish(pool); }
                    for x in w.dr.iter_mut() { x.finish(pool); }
                    for x in w.cb.iter_mut() { x.finish(pool); }
                    unsafe { _mm_sfence() };
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
                // eid -> current winning copy (ingest, loc, worker). On a repeat, the losing copy
                // (later ingest, or the equal-ingest newcomer: such copies are identical) is marked.
                let mut table: Vec<(u64, u32, u32)> = Vec::new();
                let mut twid: Vec<u8> = Vec::new();
                let mark = |wid: usize, loc: u32| {
                    if loc != NOLOC {
                        let pb = (loc >> IDX_BITS) as usize;
                        let idx = (loc & ((1 << IDX_BITS) - 1)) as usize;
                        lose[wid][loff[wid][pb] + (idx >> 6)].fetch_or(1u64 << (idx & 63), Relaxed);
                    }
                };
                loop {
                    let b = next.fetch_add(1, Relaxed);
                    if b >= NBE {
                        break;
                    }
                    let total: usize = w1s.iter().map(|w| w.dr[b].len()).sum();
                    let cap = (total + total / 2).next_power_of_two().max(16);
                    let mask = cap - 1;
                    table.clear();
                    table.resize(cap, (0, 0, 0));
                    twid.clear();
                    twid.resize(cap, 0);
                    for (wid, w) in w1s.iter().enumerate() {
                        w.dr[b].for_slices(|sl| {
                            for r in sl {
                                let mut i = ((r.eid >> 32) as usize) & mask;
                                loop {
                                    let t = unsafe { table.get_unchecked_mut(i) };
                                    if t.0 == r.eid {
                                        if r.ingest < t.1 {
                                            mark(twid[i] as usize, t.2);
                                            *t = (r.eid, r.ingest, r.loc);
                                            twid[i] = wid as u8;
                                        } else {
                                            mark(wid, r.loc);
                                        }
                                        break;
                                    }
                                    if t.0 == 0 {
                                        *t = (r.eid, r.ingest, r.loc);
                                        twid[i] = wid as u8;
                                        break;
                                    }
                                    i = (i + 1) & mask;
                                }
                            }
                        });
                    }
                    for w in &w1s {
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
    let total_ev: usize = w1s.iter().map(|w| w.pe.iter().map(|x| x.len()).sum::<usize>()).sum();
    let urcap = total_ev / nthreads / 3 + 1024;
    let cat_names_ref = &cat_names;
    let results: Vec<(Vec<CAcc>, usize)> = thread::scope(|sc| {
        let hs: Vec<_> = (0..nthreads)
            .map(|tid| {
                let (w1s, ctx, next, out_user, order, lose, loff) = (&w1s, &ctx, &next, &out_user, order, &lose, &loff);
                sc.spawn(move || {
                    let mut st = S3 {
                        // generous reservations: only touched pages cost anything, regrowth copies would
                        ur: URows {
                            nref: Vec::with_capacity(urcap),
                            day: Vec::with_capacity(urcap),
                            sessions: Vec::with_capacity(urcap),
                            events: Vec::with_capacity(urcap),
                            rev: Vec::with_capacity(urcap),
                            top: Vec::with_capacity(urcap),
                        },
                        acc: vec![CAcc::default(); (ctx.ncamp + 1) * ctx.nd],
                        ev: vec![],
                        ck: vec![],
                        starts: vec![],
                        days: vec![],
                        srev: vec![],
                        runs: vec![],
                        ckey: vec![],
                        last: vec![0; ctx.ncamp + 1],
                        sid: 0,
                        catacc: vec![],
                    };
                    let mut tmp: Vec<PEv> = Vec::new();
                    let (mut pk, mut pv, mut nr): (Vec<u64>, Vec<u64>, Vec<u64>) = (vec![], vec![], vec![]);
                    let mut cnt: Vec<u32> = Vec::new();
                    let mut pos: Vec<u32> = Vec::new();
                    loop {
                        let oi = next.fetch_add(1, Relaxed);
                        if oi >= NBP {
                            break;
                        }
                        let b = order[oi];
                        let mut ev = std::mem::take(&mut st.ev);
                        let mut ck = std::mem::take(&mut st.ck);
                        // counting-sort scatter on the top bits of pkey (skipping dedup losers),
                        // then sort each small group by (pkey, ts)
                        let ne: usize = w1s.iter().map(|w| w.pe[b].len()).sum();
                        let nc: usize = w1s.iter().map(|w| w.cb[b].len()).sum();
                        let bits = ((ne.max(nc) / 8).max(1).next_power_of_two().trailing_zeros()).clamp(1, 16);
                        let sh = 64 - bits;
                        let nsb = 1usize << bits;
                        cnt.clear();
                        cnt.resize(nsb + 1, 0);
                        for (wid, w) in w1s.iter().enumerate() {
                            // stage 2 is joined: read the bitmaps as plain words
                            let words: &[u64] = unsafe { std::mem::transmute::<&[AtomicU64], &[u64]>(&lose[wid][loff[wid][b]..]) };
                            let mut idx = 0usize;
                            w.pe[b].for_slices(|sl| {
                                for r in sl {
                                    let keep = ((unsafe { *words.get_unchecked(idx >> 6) } >> (idx & 63)) & 1) ^ 1;
                                    cnt[(r.pkey >> sh) as usize] += keep as u32;
                                    idx += 1;
                                }
                            });
                        }
                        let mut acc = 0u32;
                        for x in cnt.iter_mut() {
                            let c = *x;
                            *x = acc;
                            acc += c;
                        }
                        let kept = acc as usize;

                        for v in [&mut pk, &mut pv, &mut nr] {
                            v.clear();
                            v.reserve(kept);
                            unsafe { v.set_len(kept) };
                        }
                        pos.clear();
                        pos.extend_from_slice(&cnt);
                        for (wid, w) in w1s.iter().enumerate() {
                            // stage 2 is joined: read the bitmaps as plain words
                            let words: &[u64] = unsafe { std::mem::transmute::<&[AtomicU64], &[u64]>(&lose[wid][loff[wid][b]..]) };
                            let mut idx = 0usize;
                            w.pe[b].for_slices(|sl| {
                                for r in sl {
                                    if (unsafe { *words.get_unchecked(idx >> 6) } >> (idx & 63)) & 1 == 0 {
                                        let g = (r.pkey >> sh) as usize;
                                        let o = pos[g] as usize;
                                        unsafe {
                                            *pk.get_unchecked_mut(o) = r.pkey;
                                            *pv.get_unchecked_mut(o) = r.packed;
                                            *nr.get_unchecked_mut(o) = r.nref;
                                        }
                                        pos[g] += 1;
                                    }
                                    idx += 1;
                                }
                            });
                        }
                        for g in 0..nsb {
                            let (x, y) = (cnt[g] as usize, cnt[g + 1] as usize);
                            if y - x > 1 {
                                let k0 = pk[x];
                                if pk[x + 1..y].iter().all(|&k| k == k0) {
                                    sort_u64(&mut pv[x..y]);
                                } else {
                                    // a few persons share this group: partition by person, then sort each
                                    let mut keys = [0u64; 8];
                                    let mut nk = 0;
                                    let mut few = true;
                                    for &k in &pk[x..y] {
                                        if !keys[..nk].contains(&k) {
                                            if nk == 8 {
                                                few = false;
                                                break;
                                            }
                                            keys[nk] = k;
                                            nk += 1;
                                        }
                                    }
                                    tmp.clear();
                                    for i in x..y {
                                        tmp.push(PEv { pkey: pk[i], nref: nr[i], packed: pv[i] });
                                    }
                                    if few {
                                        keys[..nk].sort_unstable();
                                        let mut o = x;
                                        for &k in &keys[..nk] {
                                            let s0 = o;
                                            for r in tmp.iter() {
                                                if r.pkey == k {
                                                    pk[o] = k;
                                                    pv[o] = r.packed;
                                                    nr[o] = r.nref;
                                                    o += 1;
                                                }
                                            }
                                            sort_u64(&mut pv[s0..o]);
                                        }
                                    } else {
                                        tmp.sort_unstable_by(|a, b| (a.pkey, a.packed).cmp(&(b.pkey, b.packed)));
                                        for (i, r) in tmp.iter().enumerate() {
                                            pk[x + i] = r.pkey;
                                            pv[x + i] = r.packed;
                                            nr[x + i] = r.nref;
                                        }
                                    }
                                }
                            }
                        }
                        // clicks
                        cnt.clear();
                        cnt.resize(nsb + 1, 0);
                        for w in w1s.iter() {
                            w.cb[b].for_slices(|sl| {
                                for r in sl {
                                    cnt[(r.pkey >> sh) as usize] += 1;
                                }
                            });
                        }
                        let mut acc = 0u32;
                        for x in cnt.iter_mut() {
                            let c = *x;
                            *x = acc;
                            acc += c;
                        }
                        ck.clear();
                        ck.reserve(nc);
                        unsafe { ck.set_len(nc) };
                        pos.clear();
                        pos.extend_from_slice(&cnt);
                        for w in w1s.iter() {
                            w.cb[b].for_slices(|sl| {
                                for r in sl {
                                    let g = (r.pkey >> sh) as usize;
                                    unsafe { *ck.get_unchecked_mut(pos[g] as usize) = *r };
                                    pos[g] += 1;
                                }
                            });
                        }
                        for g in 0..nsb {
                            let (x, y) = (cnt[g] as usize, cnt[g + 1] as usize);
                            if y - x > 1 {
                                let g = &mut ck[x..y];
                                let k0 = g[0].pkey;
                                if g.iter().all(|c| c.pkey == k0) {
                                    g.sort_unstable_by_key(|c| c.tc);
                                } else {
                                    g.sort_unstable_by(|a, b| (a.pkey, a.tc).cmp(&(b.pkey, b.tc)));
                                }
                            }
                        }
                        let (mut i, mut c) = (0usize, 0usize);
                        let ev_n = pk.len();
                        while i < ev_n {
                            let k = pk[i];
                            let mut j = i + 1;
                            while j < ev_n && pk[j] == k {
                                j += 1;
                            }
                            let pk_ = k;
                            while c < ck.len() && ck[c].pkey < pk_ {
                                c += 1;
                            }
                            let mut ce = c;
                            while ce < ck.len() && ck[ce].pkey == pk_ {
                                ce += 1;
                            }
                            process_person(nr[i], &pv[i..j], &ck[c..ce], ctx, &mut st);
                            c = ce;
                            i = j;
                        }
                        st.ev = ev;
                        st.ck = ck;
                    }
                    // write user parquet
                    let n = st.ur.nref.len();
                    if n > 0 {
                        let mut w = pq::Writer::new(user_fields());
                        let name_bytes: usize = st.ur.nref.iter().map(|&r| (r >> 48) as usize).sum();
                        w.reserve(name_bytes + n * 40 + 4096);
                        let rg = 1 << 20;
                        let mut s = 0;
                        while s < n {
                            let e = (s + rg).min(n);
                            w.row_group(
                                &[
                                    pq::Col::Refs(&st.ur.nref[s..e]),
                                    pq::Col::I32(&st.ur.day[s..e]),
                                    pq::Col::I32(&st.ur.sessions[s..e]),
                                    pq::Col::I32(&st.ur.events[s..e]),
                                    pq::Col::I64(&st.ur.rev[s..e]),
                                    pq::Col::OptIdx(&st.ur.top[s..e], cat_names_ref),
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
