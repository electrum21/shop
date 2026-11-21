//! Minimal Parquet writer: PLAIN encoding, uncompressed, data page v1.

pub enum Col<'a> {
    I32(&'a [i32]),
    I64(&'a [i64]),
    /// Required string column: (data, offsets len+1)
    Str(&'a [&'a [u8]]),
    /// Optional string column: None = null
    OptStr(&'a [Option<&'a [u8]>]),
    /// Required string column given as packed refs (ptr | len << 48)
    Refs(&'a [u64]),
    /// Optional string column given as indexes into a name table (u16::MAX = null)
    OptIdx(&'a [u16], &'a [Vec<u8>]),
}

pub struct Field {
    pub name: &'static str,
    pub kind: Kind,
}
#[derive(Clone, Copy, PartialEq)]
pub enum Kind {
    I32,
    I64,
    Date,
    Str,
    OptStr,
}

struct Tw(Vec<u8>);
impl Tw {
    fn varint(&mut self, mut v: u64) {
        while v >= 0x80 {
            self.0.push((v as u8) | 0x80);
            v >>= 7;
        }
        self.0.push(v as u8);
    }
    fn zz32(&mut self, v: i32) {
        self.varint(((v << 1) ^ (v >> 31)) as u32 as u64);
    }
    fn zz64(&mut self, v: i64) {
        self.varint(((v << 1) ^ (v >> 63)) as u64);
    }
    fn fh(&mut self, last: &mut i16, id: i16, ty: u8) {
        let d = id - *last;
        if d > 0 && d <= 15 {
            self.0.push(((d as u8) << 4) | ty);
        } else {
            self.0.push(ty);
            self.zz32(id as i32);
        }
        *last = id;
    }
    fn i32f(&mut self, last: &mut i16, id: i16, v: i32) {
        self.fh(last, id, 5);
        self.zz32(v);
    }
    fn i64f(&mut self, last: &mut i16, id: i16, v: i64) {
        self.fh(last, id, 6);
        self.zz64(v);
    }
    fn strf(&mut self, last: &mut i16, id: i16, s: &str) {
        self.fh(last, id, 8);
        self.str(s);
    }
    fn str(&mut self, s: &str) {
        self.varint(s.len() as u64);
        self.0.extend_from_slice(s.as_bytes());
    }
    fn list(&mut self, last: &mut i16, id: i16, ty: u8, n: usize) {
        self.fh(last, id, 9);
        self.list_hdr(ty, n);
    }
    fn list_hdr(&mut self, ty: u8, n: usize) {
        if n < 15 {
            self.0.push(((n as u8) << 4) | ty);
        } else {
            self.0.push(0xF0 | ty);
            self.varint(n as u64);
        }
    }
    fn stop(&mut self) {
        self.0.push(0);
    }
    fn struct_f(&mut self, last: &mut i16, id: i16) {
        self.fh(last, id, 12);
    }
}

fn ptype(k: Kind) -> i32 {
    match k {
        Kind::I32 | Kind::Date => 1,
        Kind::I64 => 2,
        Kind::Str | Kind::OptStr => 6,
    }
}

struct ChunkInfo {
    offset: i64,
    total: i64,
    num_values: i64,
}

pub struct Writer {
    pub buf: Vec<u8>,
    page: Vec<u8>,
    fields: Vec<Field>,
    groups: Vec<(Vec<ChunkInfo>, i64)>, // chunks, num_rows
    num_rows: i64,
}

impl Writer {
    pub fn new(fields: Vec<Field>) -> Self {
        Writer { buf: b"PAR1".to_vec(), page: Vec::new(), fields, groups: vec![], num_rows: 0 }
    }
    pub fn reserve(&mut self, bytes: usize) {
        self.buf.reserve(bytes);
    }

    pub fn row_group(&mut self, cols: &[Col], nrows: usize) {
        let mut chunks = vec![];
        for (f, c) in self.fields.iter().zip(cols) {
            let mut page = std::mem::take(&mut self.page);
            page.clear();
            let nvals = nrows;
            match c {
                // little-endian target: plain encoding is the in-memory layout
                Col::I32(v) => page.extend_from_slice(unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, v.len() * 4) }),
                Col::I64(v) => page.extend_from_slice(unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, v.len() * 8) }),
                Col::Str(v) => {
                    let tot: usize = v.iter().map(|s| s.len() + 4).sum();
                    page.reserve(tot);
                    for (i, s) in v.iter().enumerate() {
                        // strings may be scattered over the input mappings: prefetch ahead
                        if i + 16 < v.len() {
                            unsafe {
                                std::arch::x86_64::_mm_prefetch(v[i + 16].as_ptr() as *const i8, std::arch::x86_64::_MM_HINT_T0)
                            };
                        }
                        page.extend_from_slice(&(s.len() as u32).to_le_bytes());
                        page.extend_from_slice(s);
                    }
                }
                Col::Refs(v) => {
                    let tot: usize = v.iter().map(|&r| (r >> 48) as usize + 4).sum();
                    page.reserve(tot);
                    for (i, &r) in v.iter().enumerate() {
                        if i + 16 < v.len() {
                            unsafe {
                                std::arch::x86_64::_mm_prefetch((v[i + 16] & 0xFFFF_FFFF_FFFF) as *const i8, std::arch::x86_64::_MM_HINT_T0)
                            };
                        }
                        let l = (r >> 48) as usize;
                        let sl = unsafe { std::slice::from_raw_parts((r & 0xFFFF_FFFF_FFFF) as *const u8, l) };
                        page.extend_from_slice(&(l as u32).to_le_bytes());
                        page.extend_from_slice(sl);
                    }
                }
                Col::OptIdx(v, names) => {
                    let groups = (v.len() + 7) / 8;
                    let mut lv = Tw(Vec::new());
                    lv.varint(((groups as u64) << 1) | 1);
                    let mut bytes = vec![0u8; groups];
                    for (i, &t) in v.iter().enumerate() {
                        if t != u16::MAX {
                            bytes[i / 8] |= 1 << (i % 8);
                        }
                    }
                    lv.0.extend_from_slice(&bytes);
                    page.extend_from_slice(&(lv.0.len() as u32).to_le_bytes());
                    page.extend_from_slice(&lv.0);
                    for &t in v.iter() {
                        if t != u16::MAX {
                            let s = &names[t as usize];
                            page.extend_from_slice(&(s.len() as u32).to_le_bytes());
                            page.extend_from_slice(s);
                        }
                    }
                }
                Col::OptStr(v) => {
                    // definition levels, RLE/bit-packed hybrid, bit width 1
                    let groups = (v.len() + 7) / 8;
                    let mut lv = Tw(Vec::new());
                    lv.varint(((groups as u64) << 1) | 1);
                    let mut bytes = vec![0u8; groups];
                    for (i, s) in v.iter().enumerate() {
                        if s.is_some() {
                            bytes[i / 8] |= 1 << (i % 8);
                        }
                    }
                    lv.0.extend_from_slice(&bytes);
                    page.extend_from_slice(&(lv.0.len() as u32).to_le_bytes());
                    page.extend_from_slice(&lv.0);
                    for s in v.iter().flatten() {
                        page.extend_from_slice(&(s.len() as u32).to_le_bytes());
                        page.extend_from_slice(s);
                    }
                }
            }
            let _ = f;
            // page header
            let mut h = Tw(Vec::new());
            let mut l = 0i16;
            h.i32f(&mut l, 1, 0); // DATA_PAGE
            h.i32f(&mut l, 2, page.len() as i32);
            h.i32f(&mut l, 3, page.len() as i32);
            h.struct_f(&mut l, 5);
            let mut l2 = 0i16;
            h.i32f(&mut l2, 1, nvals as i32);
            h.i32f(&mut l2, 2, 0); // PLAIN
            h.i32f(&mut l2, 3, 3); // RLE
            h.i32f(&mut l2, 4, 3); // RLE
            h.stop();
            h.stop();
            let offset = self.buf.len() as i64;
            self.buf.reserve(h.0.len() + page.len());
            self.buf.extend_from_slice(&h.0);
            self.buf.extend_from_slice(&page);
            chunks.push(ChunkInfo {
                offset,
                total: (h.0.len() + page.len()) as i64,
                num_values: nvals as i64,
            });
            self.page = page;
        }
        self.num_rows += nrows as i64;
        self.groups.push((chunks, nrows as i64));
    }

    pub fn finish(mut self) -> Vec<u8> {
        let mut m = Tw(Vec::new());
        let mut l = 0i16;
        m.i32f(&mut l, 1, 1);
        // schema
        m.list(&mut l, 2, 12, self.fields.len() + 1);
        {
            let mut l2 = 0i16;
            m.strf(&mut l2, 4, "schema");
            m.i32f(&mut l2, 5, self.fields.len() as i32);
            m.stop();
        }
        for f in &self.fields {
            let mut l2 = 0i16;
            m.i32f(&mut l2, 1, ptype(f.kind));
            m.i32f(&mut l2, 3, if f.kind == Kind::OptStr { 1 } else { 0 });
            m.strf(&mut l2, 4, f.name);
            match f.kind {
                Kind::Str | Kind::OptStr => {
                    m.i32f(&mut l2, 6, 0); // UTF8
                    m.struct_f(&mut l2, 10);
                    let mut l3 = 0i16;
                    m.struct_f(&mut l3, 1); // STRING
                    m.stop();
                    m.stop();
                }
                Kind::Date => {
                    m.i32f(&mut l2, 6, 6); // DATE
                    m.struct_f(&mut l2, 10);
                    let mut l3 = 0i16;
                    m.struct_f(&mut l3, 6); // DATE
                    m.stop();
                    m.stop();
                }
                _ => {}
            }
            m.stop();
        }
        m.i64f(&mut l, 3, self.num_rows);
        m.list(&mut l, 4, 12, self.groups.len());
        for (chunks, nrows) in &self.groups {
            let mut l2 = 0i16;
            m.list(&mut l2, 1, 12, chunks.len());
            let mut tot = 0;
            for (f, c) in self.fields.iter().zip(chunks) {
                tot += c.total;
                let mut l3 = 0i16;
                m.i64f(&mut l3, 2, c.offset);
                m.struct_f(&mut l3, 3);
                let mut l4 = 0i16;
                m.i32f(&mut l4, 1, ptype(f.kind));
                m.list(&mut l4, 2, 5, 2);
                m.zz32(0);
                m.zz32(3);
                m.list(&mut l4, 3, 8, 1);
                m.str(f.name);
                m.i32f(&mut l4, 4, 0); // UNCOMPRESSED
                m.i64f(&mut l4, 5, c.num_values);
                m.i64f(&mut l4, 6, c.total);
                m.i64f(&mut l4, 7, c.total);
                m.i64f(&mut l4, 9, c.offset);
                m.stop();
                m.stop();
            }
            m.i64f(&mut l2, 2, tot);
            m.i64f(&mut l2, 3, *nrows);
            m.stop();
        }
        m.strf(&mut l, 6, "sessions-rs");
        m.stop();
        let len = m.0.len() as u32;
        self.buf.extend_from_slice(&m.0);
        self.buf.extend_from_slice(&len.to_le_bytes());
        self.buf.extend_from_slice(b"PAR1");
        self.buf
    }
}
