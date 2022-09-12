// TODO: use tinyvec so e.g. SlawBuf::nil(), wee strings can be on stack
#[derive(Debug, PartialEq, Eq)]
pub struct SlawBuf(Vec<u8>);

impl SlawBuf {
    pub fn nil() -> SlawBuf {
        let oct = ((0b0010u64) << 60) | 2;
        SlawBuf(oct::to_vec(oct))
    }

    pub fn boolean(b: bool) -> SlawBuf {
        let oct = ((0b0010) << 60 ) | if b { 1 } else { 0 };
        SlawBuf(oct::to_vec(oct))
    }

    pub fn to_bytes(&self) -> &[u8] {
        &self.0
    }

    pub fn to_slaw(&self) -> &Slaw {
        Slaw::from_octs(&self.0).expect("SlawBuf broke slaw invariant, this is a bug in salat")
    }
}

use std::ops::Deref;
impl Deref for SlawBuf {
    type Target = Slaw;
    fn deref(&self) -> &Slaw {
        self.to_slaw()
    }
}

// unsized - a la Path or str
// TODO: should have a custom debug impl
#[derive(Debug, PartialEq, Eq)]
pub struct Slaw([u8]);

#[derive(Debug, PartialEq, Eq)]
pub struct InvalidSlaw;

impl Slaw {
    pub fn from_octs(octs: &[u8]) -> Result<&Slaw, InvalidSlaw> {
        if octs.len() % 8 == 0 && octs.len() >= 8 {
            let maybe_bad_slaw = unsafe { &*(octs.as_ref() as *const [u8] as *const Slaw) };
            let ilk = SlawIlk::new(&maybe_bad_slaw.0);
            match ilk {
                Ok(_) => Ok(maybe_bad_slaw),
                Err(err) => Err(err)
            }
        } else {
            Err(InvalidSlaw)
        }
    }

    pub fn to_bytes(&self) -> &[u8] {
        &self.0
    }

    // these constructors return SlawBuf. Purely for convenience
    pub fn nil() -> SlawBuf {
        SlawBuf::nil()
    }

    pub fn boolean(b: bool) -> SlawBuf {
        SlawBuf::boolean(b)
    }

    pub fn ilk(&self) -> SlawIlk {
        SlawIlk::new(&self.0).expect("Invalid slaw")
    }

    // C-like apis without generics, using Option instead of out params
    pub fn is_nil(&self) -> bool {
        self.emit::<()>().is_some()
    }
    pub fn emit_nil(&self) -> Option<()> {
        self.emit::<()>()
    }

    pub fn is_boolean(&self) -> bool {
        self.emit::<bool>().is_some()
    }
    pub fn emit_boolean(&self) -> Option<bool> {
        self.emit::<bool>()
    }

    pub fn emit<E: SlawEmit>(&self) -> Option<E> {
        SlawEmit::emit(self)
    }

    pub fn drop_nil(&self) -> Option<&Slaw> {
        if self.is_nil() {
            None
        } else {
            Some(self)
        }
    }
}

pub trait SlawEmit {
    fn emit(slaw: &Slaw) -> Option<Self> where Self: Sized;
}

impl SlawEmit for () {
    fn emit(slaw: &Slaw) -> Option<()> {
        match QuickIlk::new(slaw.to_bytes()) {
            (QuickIlk::BooleanOrNil, oct) => {
                if oct & 0b11 == 0b10 { // nil
                    Some(())
                } else { // boolean
                    None
                }
            }
            _ => None
        }
    }
}

impl SlawEmit for bool {
    fn emit(slaw: &Slaw) -> Option<bool> {
        match QuickIlk::new(slaw.to_bytes()) {
            (QuickIlk::BooleanOrNil, oct) => {
                if oct & 0b11 == 0b10 { // nil
                    None
                } else { // boolean
                    Some(oct & 0b1 == 1)
                }
            }
            _ => None
        }
    }
}

use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
#[derive(FromPrimitive)]
enum QuickIlk {
    BackwardsProtein = 0b0000,
    Protein = 0b0001,
    BooleanOrNil = 0b0010,
    WeeString = 0b0011,
    List = 0b0100,
    Map = 0b0101,
    Cons = 0b0110,
    FullString = 0b0111,
    Signed = 0b1000,
    Unsigned = 0b1001,
    Float = 0b1010,
    SingletonReserved = 0b1011,
    ArraySigned = 0b1100,
    ArrayUnsigned = 0b1101,
    ArrayFloat = 0b1110,
    ArrayReserved = 0b1111
}

impl QuickIlk {
    fn new(header: &[u8]) -> (QuickIlk, u64) {
        let oct = oct::from_bytes(header);
        let ilk = QuickIlk::from_u64(oct >> 60).expect("QuickIlk definition incomplete");
        (ilk, oct)
    }
}

#[derive(Debug, PartialEq, Eq)]
/// SlawIlk is a conveniently pattern-matchable view of a Slaw's guts
pub enum SlawIlk<'a> {
    Protein(Protein<'a>),
    Nil,
    Boolean(bool)
}

#[derive(Debug, PartialEq, Eq)]
pub struct Protein<'a> {
    descrips: &'a Slaw,
    ingests: &'a Slaw,
}

impl<'a> Protein<'a> {
    fn new(descrips: &'a Slaw, ingests: &'a Slaw) -> Protein<'a> {
        Protein {
            descrips: descrips,
            ingests: ingests
        }
    }
}

impl<'a> SlawIlk<'a> {
    // this validates the outermost layer of a slaw
    fn new(header: &'a [u8]) -> Result<SlawIlk, InvalidSlaw> {
        match QuickIlk::new(header) {
            (QuickIlk::Protein, _) => {
                let (descrips, ingests) = unimplemented!("protein");
                Ok(SlawIlk::Protein(Protein::new(descrips, ingests)))
            }
            (QuickIlk::BooleanOrNil, oct) => {
                let ilk = match oct & 11 {
                    3 => return Err(InvalidSlaw),
                    2 => SlawIlk::Nil,
                    1 => SlawIlk::Boolean(true),
                    0 => SlawIlk::Boolean(false),
                    _ => unreachable!()
                };
                Ok(ilk)
            }
            _ => { println!("{:?}", header); Err(InvalidSlaw) }
        }
    }
}

#[test]
fn test_slaw_nil() {
    let slaw_nil = Slaw::nil();
    assert_eq!(oct::to_bytes((0b0010) << 60 | 2), slaw_nil.to_bytes());
    assert_eq!(slaw_nil.ilk(), SlawIlk::Nil);
    assert!(slaw_nil.is_nil());
    assert_eq!(Some(()), slaw_nil.emit::<()>());

    // drop_nil
    assert_eq!(None, Slaw::drop_nil(&slaw_nil));
    // TODO: proptest
    let not_nil = Slaw::boolean(true);
    let not_nil = not_nil.to_slaw();
    assert_eq!(Some(not_nil), Slaw::drop_nil(not_nil));
    assert!(!not_nil.is_nil());
    assert_eq!(None, not_nil.emit_nil());
    assert_eq!(None, not_nil.emit::<()>());
}

#[test]
fn test_slaw_boolean() {
    let slaw_false = Slaw::boolean(false);
    let slaw_true = Slaw::boolean(true);
    assert_eq!(oct::to_bytes((0b0010) << 60), slaw_false.to_bytes());
    assert_eq!(oct::to_bytes((0b0010) << 60 | 1), slaw_true.to_bytes());
    assert_eq!(SlawIlk::Boolean(false), slaw_false.ilk());
    assert_eq!(SlawIlk::Boolean(true), slaw_true.ilk());
    assert_eq!(true, slaw_true.emit().unwrap());
    assert_eq!(true, slaw_true.emit_boolean().unwrap());
    assert_eq!(false, slaw_false.emit().unwrap());
    assert_eq!(false, slaw_false.emit_boolean().unwrap());
    let not_bool = Slaw::nil();
    assert_eq!(None, not_bool.emit::<bool>())
}

mod oct {
    pub type Oct = u64;

    #[cfg(test)]
    pub fn to_bytes(oct: Oct) -> [u8; 8] {
        use byteorder::{ByteOrder, NativeEndian};
        let mut buf = [0u8; 8];
        NativeEndian::write_u64(&mut buf, oct);
        buf
    }

    pub fn to_vec(oct: Oct) -> Vec<u8> {
        use byteorder::{ByteOrder, NativeEndian};
        let mut buf = vec![0u8; 8];
        NativeEndian::write_u64(&mut buf, oct);
        buf
    }

    pub fn from_bytes(bytes: &[u8]) -> Oct {
        use byteorder::{ByteOrder, NativeEndian};
        NativeEndian::read_u64(bytes)
    }
}
