#![allow(unused_imports)]
use vest::properties::*;
use vest::regular::and_then::*;
use vest::regular::bytes::*;
use vest::regular::bytes_n::*;
use vest::regular::choice::*;
use vest::regular::cond::*;
use vest::regular::depend::*;
use vest::regular::map::*;
use vest::regular::refined::*;
use vest::regular::repeat::*;
use vest::regular::tag::*;
use vest::regular::tail::*;
use vest::regular::uints::*;
use vest::utils::*;
use vstd::prelude::*;
verus! {

pub type SpecContentType = u8;

pub type ContentType = u8;

pub type ContentTypeOwned = u8;

pub type SpecContent0 = Seq<u8>;

pub type Content0<'a> = &'a [u8];

pub type Content0Owned = Vec<u8>;

pub enum SpecMsgCF4 {
    C0(SpecContent0),
    C1(u16),
    C2(u32),
    Unrecognized(Seq<u8>),
}

pub type SpecMsgCF4Inner = Either<SpecContent0, Either<u16, Either<u32, Seq<u8>>>>;

impl SpecFrom<SpecMsgCF4> for SpecMsgCF4Inner {
    open spec fn spec_from(m: SpecMsgCF4) -> SpecMsgCF4Inner {
        match m {
            SpecMsgCF4::C0(m) => Either::Left(m),
            SpecMsgCF4::C1(m) => Either::Right(Either::Left(m)),
            SpecMsgCF4::C2(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecMsgCF4::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }
}

impl SpecFrom<SpecMsgCF4Inner> for SpecMsgCF4 {
    open spec fn spec_from(m: SpecMsgCF4Inner) -> SpecMsgCF4 {
        match m {
            Either::Left(m) => SpecMsgCF4::C0(m),
            Either::Right(Either::Left(m)) => SpecMsgCF4::C1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecMsgCF4::C2(m),
            Either::Right(Either::Right(Either::Right(m))) => SpecMsgCF4::Unrecognized(m),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MsgCF4<'a> {
    C0(Content0<'a>),
    C1(u16),
    C2(u32),
    Unrecognized(&'a [u8]),
}

pub type MsgCF4Inner<'a> = Either<Content0<'a>, Either<u16, Either<u32, &'a [u8]>>>;

impl View for MsgCF4<'_> {
    type V = SpecMsgCF4;

    open spec fn view(&self) -> Self::V {
        match self {
            MsgCF4::C0(m) => SpecMsgCF4::C0(m@),
            MsgCF4::C1(m) => SpecMsgCF4::C1(m@),
            MsgCF4::C2(m) => SpecMsgCF4::C2(m@),
            MsgCF4::Unrecognized(m) => SpecMsgCF4::Unrecognized(m@),
        }
    }
}

impl<'a> From<MsgCF4<'a>> for MsgCF4Inner<'a> {
    fn ex_from(m: MsgCF4<'a>) -> MsgCF4Inner<'a> {
        match m {
            MsgCF4::C0(m) => Either::Left(m),
            MsgCF4::C1(m) => Either::Right(Either::Left(m)),
            MsgCF4::C2(m) => Either::Right(Either::Right(Either::Left(m))),
            MsgCF4::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }
}

impl<'a> From<MsgCF4Inner<'a>> for MsgCF4<'a> {
    fn ex_from(m: MsgCF4Inner<'a>) -> MsgCF4<'a> {
        match m {
            Either::Left(m) => MsgCF4::C0(m),
            Either::Right(Either::Left(m)) => MsgCF4::C1(m),
            Either::Right(Either::Right(Either::Left(m))) => MsgCF4::C2(m),
            Either::Right(Either::Right(Either::Right(m))) => MsgCF4::Unrecognized(m),
        }
    }
}

pub struct MsgCF4Mapper;

impl View for MsgCF4Mapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MsgCF4Mapper {
    type Src = SpecMsgCF4Inner;

    type Dst = SpecMsgCF4;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for MsgCF4Mapper {
    type Src<'a> = MsgCF4Inner<'a>;

    type Dst<'a> = MsgCF4<'a>;

    type SrcOwned = MsgCF4OwnedInner;

    type DstOwned = MsgCF4Owned;
}

pub enum MsgCF4Owned {
    C0(Content0Owned),
    C1(u16),
    C2(u32),
    Unrecognized(Vec<u8>),
}

pub type MsgCF4OwnedInner = Either<Content0Owned, Either<u16, Either<u32, Vec<u8>>>>;

impl View for MsgCF4Owned {
    type V = SpecMsgCF4;

    open spec fn view(&self) -> Self::V {
        match self {
            MsgCF4Owned::C0(m) => SpecMsgCF4::C0(m@),
            MsgCF4Owned::C1(m) => SpecMsgCF4::C1(m@),
            MsgCF4Owned::C2(m) => SpecMsgCF4::C2(m@),
            MsgCF4Owned::Unrecognized(m) => SpecMsgCF4::Unrecognized(m@),
        }
    }
}

impl From<MsgCF4Owned> for MsgCF4OwnedInner {
    fn ex_from(m: MsgCF4Owned) -> MsgCF4OwnedInner {
        match m {
            MsgCF4Owned::C0(m) => Either::Left(m),
            MsgCF4Owned::C1(m) => Either::Right(Either::Left(m)),
            MsgCF4Owned::C2(m) => Either::Right(Either::Right(Either::Left(m))),
            MsgCF4Owned::Unrecognized(m) => Either::Right(Either::Right(Either::Right(m))),
        }
    }
}

impl From<MsgCF4OwnedInner> for MsgCF4Owned {
    fn ex_from(m: MsgCF4OwnedInner) -> MsgCF4Owned {
        match m {
            Either::Left(m) => MsgCF4Owned::C0(m),
            Either::Right(Either::Left(m)) => MsgCF4Owned::C1(m),
            Either::Right(Either::Right(Either::Left(m))) => MsgCF4Owned::C2(m),
            Either::Right(Either::Right(Either::Right(m))) => MsgCF4Owned::Unrecognized(m),
        }
    }
}

pub struct SpecMsgC {
    pub f2: SpecContentType,
    pub f3: u24,
    pub f4: SpecMsgCF4,
}

pub type SpecMsgCInner = ((SpecContentType, u24), SpecMsgCF4);

impl SpecFrom<SpecMsgC> for SpecMsgCInner {
    open spec fn spec_from(m: SpecMsgC) -> SpecMsgCInner {
        ((m.f2, m.f3), m.f4)
    }
}

impl SpecFrom<SpecMsgCInner> for SpecMsgC {
    open spec fn spec_from(m: SpecMsgCInner) -> SpecMsgC {
        let ((f2, f3), f4) = m;
        SpecMsgC { f2, f3, f4 }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MsgC<'a> {
    pub f2: ContentType,
    pub f3: u24,
    pub f4: MsgCF4<'a>,
}

pub type MsgCInner<'a> = ((ContentType, u24), MsgCF4<'a>);

impl View for MsgC<'_> {
    type V = SpecMsgC;

    open spec fn view(&self) -> Self::V {
        SpecMsgC { f2: self.f2@, f3: self.f3@, f4: self.f4@ }
    }
}

impl<'a> From<MsgC<'a>> for MsgCInner<'a> {
    fn ex_from(m: MsgC<'a>) -> MsgCInner<'a> {
        ((m.f2, m.f3), m.f4)
    }
}

impl<'a> From<MsgCInner<'a>> for MsgC<'a> {
    fn ex_from(m: MsgCInner<'a>) -> MsgC<'a> {
        let ((f2, f3), f4) = m;
        MsgC { f2, f3, f4 }
    }
}

pub struct MsgCMapper;

impl View for MsgCMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MsgCMapper {
    type Src = SpecMsgCInner;

    type Dst = SpecMsgC;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for MsgCMapper {
    type Src<'a> = MsgCInner<'a>;

    type Dst<'a> = MsgC<'a>;

    type SrcOwned = MsgCOwnedInner;

    type DstOwned = MsgCOwned;
}

pub struct MsgCOwned {
    pub f2: ContentTypeOwned,
    pub f3: u24,
    pub f4: MsgCF4Owned,
}

pub type MsgCOwnedInner = ((ContentTypeOwned, u24), MsgCF4Owned);

impl View for MsgCOwned {
    type V = SpecMsgC;

    open spec fn view(&self) -> Self::V {
        SpecMsgC { f2: self.f2@, f3: self.f3@, f4: self.f4@ }
    }
}

impl From<MsgCOwned> for MsgCOwnedInner {
    fn ex_from(m: MsgCOwned) -> MsgCOwnedInner {
        ((m.f2, m.f3), m.f4)
    }
}

impl From<MsgCOwnedInner> for MsgCOwned {
    fn ex_from(m: MsgCOwnedInner) -> MsgCOwned {
        let ((f2, f3), f4) = m;
        MsgCOwned { f2, f3, f4 }
    }
}

pub struct SpecMsgD {
    pub f1: Seq<u8>,
    pub f2: u16,
}

pub type SpecMsgDInner = (Seq<u8>, u16);

impl SpecFrom<SpecMsgD> for SpecMsgDInner {
    open spec fn spec_from(m: SpecMsgD) -> SpecMsgDInner {
        (m.f1, m.f2)
    }
}

impl SpecFrom<SpecMsgDInner> for SpecMsgD {
    open spec fn spec_from(m: SpecMsgDInner) -> SpecMsgD {
        let (f1, f2) = m;
        SpecMsgD { f1, f2 }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MsgD<'a> {
    pub f1: &'a [u8],
    pub f2: u16,
}

pub type MsgDInner<'a> = (&'a [u8], u16);

impl View for MsgD<'_> {
    type V = SpecMsgD;

    open spec fn view(&self) -> Self::V {
        SpecMsgD { f1: self.f1@, f2: self.f2@ }
    }
}

impl<'a> From<MsgD<'a>> for MsgDInner<'a> {
    fn ex_from(m: MsgD<'a>) -> MsgDInner<'a> {
        (m.f1, m.f2)
    }
}

impl<'a> From<MsgDInner<'a>> for MsgD<'a> {
    fn ex_from(m: MsgDInner<'a>) -> MsgD<'a> {
        let (f1, f2) = m;
        MsgD { f1, f2 }
    }
}

pub struct MsgDMapper;

impl View for MsgDMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MsgDMapper {
    type Src = SpecMsgDInner;

    type Dst = SpecMsgD;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for MsgDMapper {
    type Src<'a> = MsgDInner<'a>;

    type Dst<'a> = MsgD<'a>;

    type SrcOwned = MsgDOwnedInner;

    type DstOwned = MsgDOwned;
}

pub struct MsgDOwned {
    pub f1: Vec<u8>,
    pub f2: u16,
}

pub type MsgDOwnedInner = (Vec<u8>, u16);

impl View for MsgDOwned {
    type V = SpecMsgD;

    open spec fn view(&self) -> Self::V {
        SpecMsgD { f1: self.f1@, f2: self.f2@ }
    }
}

impl From<MsgDOwned> for MsgDOwnedInner {
    fn ex_from(m: MsgDOwned) -> MsgDOwnedInner {
        (m.f1, m.f2)
    }
}

impl From<MsgDOwnedInner> for MsgDOwned {
    fn ex_from(m: MsgDOwnedInner) -> MsgDOwned {
        let (f1, f2) = m;
        MsgDOwned { f1, f2 }
    }
}

pub struct SpecMsgB {
    pub f1: SpecMsgD,
}

pub type SpecMsgBInner = SpecMsgD;

impl SpecFrom<SpecMsgB> for SpecMsgBInner {
    open spec fn spec_from(m: SpecMsgB) -> SpecMsgBInner {
        m.f1
    }
}

impl SpecFrom<SpecMsgBInner> for SpecMsgB {
    open spec fn spec_from(m: SpecMsgBInner) -> SpecMsgB {
        let f1 = m;
        SpecMsgB { f1 }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MsgB<'a> {
    pub f1: MsgD<'a>,
}

pub type MsgBInner<'a> = MsgD<'a>;

impl View for MsgB<'_> {
    type V = SpecMsgB;

    open spec fn view(&self) -> Self::V {
        SpecMsgB { f1: self.f1@ }
    }
}

impl<'a> From<MsgB<'a>> for MsgBInner<'a> {
    fn ex_from(m: MsgB<'a>) -> MsgBInner<'a> {
        m.f1
    }
}

impl<'a> From<MsgBInner<'a>> for MsgB<'a> {
    fn ex_from(m: MsgBInner<'a>) -> MsgB<'a> {
        let f1 = m;
        MsgB { f1 }
    }
}

pub struct MsgBMapper;

impl View for MsgBMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MsgBMapper {
    type Src = SpecMsgBInner;

    type Dst = SpecMsgB;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for MsgBMapper {
    type Src<'a> = MsgBInner<'a>;

    type Dst<'a> = MsgB<'a>;

    type SrcOwned = MsgBOwnedInner;

    type DstOwned = MsgBOwned;
}

pub struct MsgBOwned {
    pub f1: MsgDOwned,
}

pub type MsgBOwnedInner = MsgDOwned;

impl View for MsgBOwned {
    type V = SpecMsgB;

    open spec fn view(&self) -> Self::V {
        SpecMsgB { f1: self.f1@ }
    }
}

impl From<MsgBOwned> for MsgBOwnedInner {
    fn ex_from(m: MsgBOwned) -> MsgBOwnedInner {
        m.f1
    }
}

impl From<MsgBOwnedInner> for MsgBOwned {
    fn ex_from(m: MsgBOwnedInner) -> MsgBOwned {
        let f1 = m;
        MsgBOwned { f1 }
    }
}

pub struct SpecMsgA {
    pub f1: SpecMsgB,
    pub f2: Seq<u8>,
}

pub type SpecMsgAInner = (SpecMsgB, Seq<u8>);

impl SpecFrom<SpecMsgA> for SpecMsgAInner {
    open spec fn spec_from(m: SpecMsgA) -> SpecMsgAInner {
        (m.f1, m.f2)
    }
}

impl SpecFrom<SpecMsgAInner> for SpecMsgA {
    open spec fn spec_from(m: SpecMsgAInner) -> SpecMsgA {
        let (f1, f2) = m;
        SpecMsgA { f1, f2 }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MsgA<'a> {
    pub f1: MsgB<'a>,
    pub f2: &'a [u8],
}

pub type MsgAInner<'a> = (MsgB<'a>, &'a [u8]);

impl View for MsgA<'_> {
    type V = SpecMsgA;

    open spec fn view(&self) -> Self::V {
        SpecMsgA { f1: self.f1@, f2: self.f2@ }
    }
}

impl<'a> From<MsgA<'a>> for MsgAInner<'a> {
    fn ex_from(m: MsgA<'a>) -> MsgAInner<'a> {
        (m.f1, m.f2)
    }
}

impl<'a> From<MsgAInner<'a>> for MsgA<'a> {
    fn ex_from(m: MsgAInner<'a>) -> MsgA<'a> {
        let (f1, f2) = m;
        MsgA { f1, f2 }
    }
}

pub struct MsgAMapper;

impl View for MsgAMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecIso for MsgAMapper {
    type Src = SpecMsgAInner;

    type Dst = SpecMsgA;

    proof fn spec_iso(s: Self::Src) {
    }

    proof fn spec_iso_rev(s: Self::Dst) {
    }
}

impl Iso for MsgAMapper {
    type Src<'a> = MsgAInner<'a>;

    type Dst<'a> = MsgA<'a>;

    type SrcOwned = MsgAOwnedInner;

    type DstOwned = MsgAOwned;
}

pub struct MsgAOwned {
    pub f1: MsgBOwned,
    pub f2: Vec<u8>,
}

pub type MsgAOwnedInner = (MsgBOwned, Vec<u8>);

impl View for MsgAOwned {
    type V = SpecMsgA;

    open spec fn view(&self) -> Self::V {
        SpecMsgA { f1: self.f1@, f2: self.f2@ }
    }
}

impl From<MsgAOwned> for MsgAOwnedInner {
    fn ex_from(m: MsgAOwned) -> MsgAOwnedInner {
        (m.f1, m.f2)
    }
}

impl From<MsgAOwnedInner> for MsgAOwned {
    fn ex_from(m: MsgAOwnedInner) -> MsgAOwned {
        let (f1, f2) = m;
        MsgAOwned { f1, f2 }
    }
}

pub struct SpecContentTypeCombinator(U8);

impl SpecCombinator for SpecContentTypeCombinator {
    type SpecResult = SpecContentType;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecContentTypeCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecContentTypeCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecContentTypeCombinatorAlias = U8;

pub struct ContentTypeCombinator(U8);

impl View for ContentTypeCombinator {
    type V = SpecContentTypeCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecContentTypeCombinator(self.0@)
    }
}

impl Combinator for ContentTypeCombinator {
    type Result<'a> = ContentType;

    type Owned = ContentTypeOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type ContentTypeCombinatorAlias = U8;

pub struct SpecContent0Combinator(Bytes);

impl SpecCombinator for SpecContent0Combinator {
    type SpecResult = SpecContent0;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecContent0Combinator {
    open spec fn is_prefix_secure() -> bool {
        SpecContent0CombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecContent0CombinatorAlias = Bytes;

pub struct Content0Combinator(Bytes);

impl View for Content0Combinator {
    type V = SpecContent0Combinator;

    closed spec fn view(&self) -> Self::V {
        SpecContent0Combinator(self.0@)
    }
}

impl Combinator for Content0Combinator {
    type Result<'a> = Content0<'a>;

    type Owned = Content0Owned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type Content0CombinatorAlias = Bytes;

pub struct SpecMsgCF4Combinator(
    AndThen<
        Bytes,
        Mapped<
            OrdChoice<
                Cond<SpecContent0Combinator>,
                OrdChoice<Cond<U16Be>, OrdChoice<Cond<U32Be>, Cond<Tail>>>,
            >,
            MsgCF4Mapper,
        >,
    >,
);

impl SpecCombinator for SpecMsgCF4Combinator {
    type SpecResult = SpecMsgCF4;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecMsgCF4Combinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMsgCF4CombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecMsgCF4CombinatorAlias = AndThen<
    Bytes,
    Mapped<
        OrdChoice<
            Cond<SpecContent0Combinator>,
            OrdChoice<Cond<U16Be>, OrdChoice<Cond<U32Be>, Cond<Tail>>>,
        >,
        MsgCF4Mapper,
    >,
>;

pub struct MsgCF4Combinator(
    AndThen<
        Bytes,
        Mapped<
            OrdChoice<
                Cond<Content0Combinator>,
                OrdChoice<Cond<U16Be>, OrdChoice<Cond<U32Be>, Cond<Tail>>>,
            >,
            MsgCF4Mapper,
        >,
    >,
);

impl View for MsgCF4Combinator {
    type V = SpecMsgCF4Combinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsgCF4Combinator(self.0@)
    }
}

impl Combinator for MsgCF4Combinator {
    type Result<'a> = MsgCF4<'a>;

    type Owned = MsgCF4Owned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type MsgCF4CombinatorAlias = AndThen<
    Bytes,
    Mapped<
        OrdChoice<
            Cond<Content0Combinator>,
            OrdChoice<Cond<U16Be>, OrdChoice<Cond<U32Be>, Cond<Tail>>>,
        >,
        MsgCF4Mapper,
    >,
>;

pub struct SpecMsgCCombinator(
    Mapped<SpecDepend<(SpecContentTypeCombinator, U24Be), SpecMsgCF4Combinator>, MsgCMapper>,
);

impl SpecCombinator for SpecMsgCCombinator {
    type SpecResult = SpecMsgC;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecMsgCCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMsgCCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecMsgCCombinatorAlias = Mapped<
    SpecDepend<(SpecContentTypeCombinator, U24Be), SpecMsgCF4Combinator>,
    MsgCMapper,
>;

pub struct MsgCCont;

pub struct MsgCCombinator(
    Mapped<Depend<(ContentTypeCombinator, U24Be), MsgCF4Combinator, MsgCCont>, MsgCMapper>,
);

impl View for MsgCCombinator {
    type V = SpecMsgCCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsgCCombinator(self.0@)
    }
}

impl Combinator for MsgCCombinator {
    type Result<'a> = MsgC<'a>;

    type Owned = MsgCOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type MsgCCombinatorAlias = Mapped<
    Depend<(ContentTypeCombinator, U24Be), MsgCF4Combinator, MsgCCont>,
    MsgCMapper,
>;

pub spec const SPEC_MSGD_F1: Seq<u8> = seq![1; 4];

pub const MSGD_F2: u16 = 4660;

pub struct SpecMsgDCombinator(
    Mapped<
        (Refined<BytesN<4>, BytesPredicate16235736133663645624>, Refined<U16Be, TagPred<u16>>),
        MsgDMapper,
    >,
);

impl SpecCombinator for SpecMsgDCombinator {
    type SpecResult = SpecMsgD;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecMsgDCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMsgDCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecMsgDCombinatorAlias = Mapped<
    (Refined<BytesN<4>, BytesPredicate16235736133663645624>, Refined<U16Be, TagPred<u16>>),
    MsgDMapper,
>;

pub exec const MSGD_F1: [u8; 4]
    ensures
        MSGD_F1@ == SPEC_MSGD_F1,
{
    let arr: [u8; 4] = [1;4];
    assert(arr@ == SPEC_MSGD_F1);
    arr
}

pub struct BytesPredicate16235736133663645624;

impl View for BytesPredicate16235736133663645624 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPred for BytesPredicate16235736133663645624 {
    type Input = Seq<u8>;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        i == &SPEC_MSGD_F1
    }
}

impl Pred for BytesPredicate16235736133663645624 {
    type Input<'a> = &'a [u8];

    type InputOwned = Vec<u8>;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        compare_slice(i, MSGD_F1.as_slice())
    }
}

pub struct MsgDCombinator(
    Mapped<
        (Refined<BytesN<4>, BytesPredicate16235736133663645624>, Refined<U16Be, TagPred<u16>>),
        MsgDMapper,
    >,
);

impl View for MsgDCombinator {
    type V = SpecMsgDCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsgDCombinator(self.0@)
    }
}

impl Combinator for MsgDCombinator {
    type Result<'a> = MsgD<'a>;

    type Owned = MsgDOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type MsgDCombinatorAlias = Mapped<
    (Refined<BytesN<4>, BytesPredicate16235736133663645624>, Refined<U16Be, TagPred<u16>>),
    MsgDMapper,
>;

pub struct SpecMsgBCombinator(Mapped<SpecMsgDCombinator, MsgBMapper>);

impl SpecCombinator for SpecMsgBCombinator {
    type SpecResult = SpecMsgB;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecMsgBCombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMsgBCombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecMsgBCombinatorAlias = Mapped<SpecMsgDCombinator, MsgBMapper>;

pub struct MsgBCombinator(Mapped<MsgDCombinator, MsgBMapper>);

impl View for MsgBCombinator {
    type V = SpecMsgBCombinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsgBCombinator(self.0@)
    }
}

impl Combinator for MsgBCombinator {
    type Result<'a> = MsgB<'a>;

    type Owned = MsgBOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type MsgBCombinatorAlias = Mapped<MsgDCombinator, MsgBMapper>;

pub struct SpecMsgACombinator(Mapped<(SpecMsgBCombinator, Tail), MsgAMapper>);

impl SpecCombinator for SpecMsgACombinator {
    type SpecResult = SpecMsgA;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl SecureSpecCombinator for SpecMsgACombinator {
    open spec fn is_prefix_secure() -> bool {
        SpecMsgACombinatorAlias::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }
}

pub type SpecMsgACombinatorAlias = Mapped<(SpecMsgBCombinator, Tail), MsgAMapper>;

pub struct MsgACombinator(Mapped<(MsgBCombinator, Tail), MsgAMapper>);

impl View for MsgACombinator {
    type V = SpecMsgACombinator;

    closed spec fn view(&self) -> Self::V {
        SpecMsgACombinator(self.0@)
    }
}

impl Combinator for MsgACombinator {
    type Result<'a> = MsgA<'a>;

    type Owned = MsgAOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    closed spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        self.0.parse(s)
    }

    closed spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v, data, pos)
    }
}

pub type MsgACombinatorAlias = Mapped<(MsgBCombinator, Tail), MsgAMapper>;

pub closed spec fn spec_content_type() -> SpecContentTypeCombinator {
    SpecContentTypeCombinator(U8)
}

pub fn content_type() -> (o: ContentTypeCombinator)
    ensures
        o@ == spec_content_type(),
{
    ContentTypeCombinator(U8)
}

pub closed spec fn spec_content_0(num: u24) -> SpecContent0Combinator {
    SpecContent0Combinator(Bytes(num.spec_into()))
}

pub fn content_0<'a>(num: u24) -> (o: Content0Combinator)
    ensures
        o@ == spec_content_0(num@),
{
    Content0Combinator(Bytes(num.ex_into()))
}

pub closed spec fn spec_msg_c_f4(f3: u24, f2: SpecContentType) -> SpecMsgCF4Combinator {
    SpecMsgCF4Combinator(
        AndThen(
            Bytes(f3.spec_into()),
            Mapped {
                inner: OrdChoice(
                    Cond { cond: f2 == 0, inner: spec_content_0(f3) },
                    OrdChoice(
                        Cond { cond: f2 == 1, inner: U16Be },
                        OrdChoice(
                            Cond { cond: f2 == 2, inner: U32Be },
                            Cond { cond: !(f2 == 0 || f2 == 1 || f2 == 2), inner: Tail },
                        ),
                    ),
                ),
                mapper: MsgCF4Mapper,
            },
        ),
    )
}

pub fn msg_c_f4<'a>(f3: u24, f2: ContentType) -> (o: MsgCF4Combinator)
    ensures
        o@ == spec_msg_c_f4(f3@, f2@),
{
    MsgCF4Combinator(
        AndThen(
            Bytes(f3.ex_into()),
            Mapped {
                inner: OrdChoice(
                    Cond { cond: f2 == 0, inner: content_0(f3) },
                    OrdChoice(
                        Cond { cond: f2 == 1, inner: U16Be },
                        OrdChoice(
                            Cond { cond: f2 == 2, inner: U32Be },
                            Cond { cond: !(f2 == 0 || f2 == 1 || f2 == 2), inner: Tail },
                        ),
                    ),
                ),
                mapper: MsgCF4Mapper,
            },
        ),
    )
}

pub closed spec fn spec_msg_c() -> SpecMsgCCombinator {
    SpecMsgCCombinator(
        Mapped {
            inner: SpecDepend {
                fst: (spec_content_type(), U24Be),
                snd: |deps| spec_msg_c_cont(deps),
            },
            mapper: MsgCMapper,
        },
    )
}

pub open spec fn spec_msg_c_cont(deps: (SpecContentType, u24)) -> SpecMsgCF4Combinator {
    let (f2, f3) = deps;
    spec_msg_c_f4(f3, f2)
}

pub fn msg_c() -> (o: MsgCCombinator)
    ensures
        o@ == spec_msg_c(),
{
    MsgCCombinator(
        Mapped {
            inner: Depend {
                fst: (content_type(), U24Be),
                snd: MsgCCont,
                spec_snd: Ghost(|deps| spec_msg_c_cont(deps)),
            },
            mapper: MsgCMapper,
        },
    )
}

impl Continuation<(ContentType, u24)> for MsgCCont {
    type Output = MsgCF4Combinator;

    open spec fn requires(&self, deps: (ContentType, u24)) -> bool {
        true
    }

    open spec fn ensures(&self, deps: (ContentType, u24), o: Self::Output) -> bool {
        o@ == spec_msg_c_cont(deps@)
    }

    fn apply(&self, deps: (ContentType, u24)) -> Self::Output {
        let (f2, f3) = deps;
        msg_c_f4(f3, f2)
    }
}

pub closed spec fn spec_msg_d() -> SpecMsgDCombinator {
    SpecMsgDCombinator(
        Mapped {
            inner: (
                Refined { inner: BytesN::<4>, predicate: BytesPredicate16235736133663645624 },
                Refined { inner: U16Be, predicate: TagPred(MSGD_F2) },
            ),
            mapper: MsgDMapper,
        },
    )
}

pub fn msg_d() -> (o: MsgDCombinator)
    ensures
        o@ == spec_msg_d(),
{
    MsgDCombinator(
        Mapped {
            inner: (
                Refined { inner: BytesN::<4>, predicate: BytesPredicate16235736133663645624 },
                Refined { inner: U16Be, predicate: TagPred(MSGD_F2) },
            ),
            mapper: MsgDMapper,
        },
    )
}

pub closed spec fn spec_msg_b() -> SpecMsgBCombinator {
    SpecMsgBCombinator(Mapped { inner: spec_msg_d(), mapper: MsgBMapper })
}

pub fn msg_b() -> (o: MsgBCombinator)
    ensures
        o@ == spec_msg_b(),
{
    MsgBCombinator(Mapped { inner: msg_d(), mapper: MsgBMapper })
}

pub closed spec fn spec_msg_a() -> SpecMsgACombinator {
    SpecMsgACombinator(Mapped { inner: (spec_msg_b(), Tail), mapper: MsgAMapper })
}

pub fn msg_a() -> (o: MsgACombinator)
    ensures
        o@ == spec_msg_a(),
{
    MsgACombinator(Mapped { inner: (msg_b(), Tail), mapper: MsgAMapper })
}

} // verus!
