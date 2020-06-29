#![forbid(unsafe_code)]

use std::{
    cmp::Ordering,
    convert::{self, TryInto},
    fmt, process,
    str::FromStr,
};

struct Options {
    /// The network pools that are searched for the network to be allocated.
    pools: Vec<Subnet>,
    /// When considering existing networks ignore these as bogus.
    ignored: Vec<Subnet>,
    /// This is the size of the network to be allocated expressed as the CIDR
    /// prefix length.
    size: PrefixLength,
}

fn main() {
    let options = parse_args();
    let existing = match fetch_subnets() {
        Ok(subnets) => subnets,
        Err(e) => {
            eprintln!("error: {:?}", e);
            std::process::exit(1)
        }
    };
    let to_avoid = existing
        .into_iter()
        .filter(|n| {
            for i in options.ignored.iter() {
                if n == i {
                    return false;
                }
            }
            true
        })
        .collect::<Vec<_>>();
    let does_clash = |n: &Subnet| -> bool {
        for a in to_avoid.iter() {
            if n.overlaps(a) {
                return true;
            }
        }
        false
    };
    let found = options
        .pools
        .iter()
        .flat_map(|pool| pool.subnets(options.size))
        .find(|n| !does_clash(&n));
    match found {
        Some(network) => {
            print!("{}", network);
            process::exit(0);
        }
        None => {
            process::exit(1);
        }
    }
}

fn parse_args() -> Options {
    use clap::{value_t_or_exit, values_t_or_exit, App, Arg};
    let matches = App::new(env!("CARGO_PKG_NAME"))
        .version(env!("CARGO_PKG_VERSION"))
        .about("Finds unallocated subnet from given network pools")
        .arg(
            Arg::with_name("pool")
                .short("p")
                .long("pool")
                .value_name("CIDR")
                .required(true)
                .multiple(true)
                .help("Determines network pool from which allocate a subnet."),
        )
        .arg(
            Arg::with_name("size")
                .short("s")
                .long("size")
                .value_name("PREFIX-LENGTH")
                .default_value("24")
                .help(
                    "The size of the allocated subnet expressed as the CIDR \
                     prefix length.",
                ),
        )
        .arg(
            Arg::with_name("ignore")
                .short("i")
                .long("ignore")
                .value_name("CIDR")
                .required(false)
                .multiple(true)
                .help("Ignore these existing networks."),
        )
        .get_matches();
    Options {
        pools: values_t_or_exit!(matches, "pool", Subnet),
        ignored: if matches.is_present("ignore") {
            values_t_or_exit!(matches, "ignore", Subnet)
        } else {
            vec![]
        },
        size: value_t_or_exit!(matches, "size", PrefixLength),
    }
}

//
// Network block
//

#[derive(Debug)]
struct Subnet {
    /// The first IPv4 address within its CIDR block belonging to the network.
    base: IPv4,
    /// The prefix mask length.
    len: PrefixLength,
}

impl Subnet {
    /// Constructs a new network block.
    fn new(base: IPv4, len: PrefixLength) -> Self {
        Self { base, len }
    }

    /// Return the first address in this network block.
    fn block_start(&self) -> IPv4 {
        if self.len.0 < 32 {
            IPv4(self.base.0 & !(u32::MAX >> self.len.0))
        } else {
            self.base
        }
    }

    /// Return the first address in this network block.
    fn first(&self) -> IPv4 {
        self.base
    }

    /// Return the last address in this network block.
    fn last(&self) -> IPv4 {
        if self.len.0 < 32 {
            let x = u32::MAX >> self.len.0;
            IPv4((self.base.0 & !x) + x)
        } else {
            self.base
        }
    }

    /// Does this network block contain the `other` network block entirely?
    fn contains(&self, other: &Self) -> bool {
        self.block_start() <= other.block_start()
            && self.first() <= other.first()
            && other.last() <= self.last()
    }

    /// Does this network block overlaps with the `other` network block?
    fn overlaps(&self, other: &Self) -> bool {
        !(self < other || other < self)
    }

    /// Return the adjacent (above) network block the same prefix length as
    /// `self`.
    fn adj(&self) -> Option<Self> {
        self.last().adj().map(|base| Self { base, len: self.len })
    }

    /// Return iterator over the subnets with the prefix length of `len`
    /// contained within `self`.
    fn subnets(&self, len: PrefixLength) -> Subnets {
        let n = Self { base: self.first(), len };
        Subnets {
            current: if self.contains(&n) { Some(n) } else { None },
            cap: self.last(),
        }
    }
}

impl PartialEq<Subnet> for Subnet {
    fn eq(&self, other: &Self) -> bool {
        self.first() == other.first() && self.last() == other.last()
    }
}

impl PartialOrd<Subnet> for Subnet {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.first() == other.first() && self.last() == other.last() {
            Some(Ordering::Equal)
        } else if self.last() < other.first() {
            Some(Ordering::Less)
        } else if other.last() < self.first() {
            Some(Ordering::Greater)
        } else {
            None
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
struct ParseSubnetError;

impl FromStr for Subnet {
    type Err = ParseSubnetError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut i = s.split('/');
        let base = i
            .next()
            .ok_or(ParseSubnetError)?
            .parse()
            .map_err(|_| ParseSubnetError)?;
        let s_len = i.next().ok_or(ParseSubnetError)?;
        if i.next().is_some() {
            return Err(ParseSubnetError);
        }
        Ok(Subnet::new(base, s_len.parse().map_err(|_| ParseSubnetError)?))
    }
}

impl fmt::Display for Subnet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}/{}", self.base, self.len)
    }
}

//
// Iterating over sub-networks of network
//

struct Subnets {
    current: Option<Subnet>,
    cap: IPv4,
}

impl Iterator for Subnets {
    type Item = Subnet;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.current.take();
        self.current = result.as_ref().and_then(|n| n.adj()).and_then(|n| {
            if n.last() <= self.cap {
                Some(n)
            } else {
                None
            }
        });
        result
    }
}

//
// IPv4 addresses
//

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct IPv4(u32);

impl IPv4 {
    fn new(a: u8, b: u8, c: u8, d: u8) -> Self {
        let a = (a as u32) << 24;
        let b = (b as u32) << 16;
        let c = (c as u32) << 8;
        let d = d as u32;
        Self(a + b + c + d)
    }

    fn a(&self) -> u8 {
        (self.0 >> 24) as u8
    }

    fn b(&self) -> u8 {
        ((self.0 >> 16) & 0xFF) as u8
    }

    fn c(&self) -> u8 {
        ((self.0 >> 8) & 0xFF) as u8
    }

    fn d(&self) -> u8 {
        (self.0 & 0xFF) as u8
    }

    fn adj(&self) -> Option<Self> {
        if self.0 < u32::MAX {
            Some(Self(self.0 + 1))
        } else {
            None
        }
    }
}

impl From<&[u8; 4]> for IPv4 {
    fn from(tup: &[u8; 4]) -> Self {
        Self::new(tup[0], tup[1], tup[2], tup[3])
    }
}

#[derive(Clone, Debug, PartialEq)]
struct ParseIPv4Error;

impl FromStr for IPv4 {
    type Err = ParseIPv4Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut i = s.split('.');
        fn p(i: &mut std::str::Split<char>) -> Result<u8, ParseIPv4Error> {
            i.next()
                .ok_or(ParseIPv4Error)?
                .parse::<u8>()
                .map_err(|_| ParseIPv4Error)
        }
        let addr = IPv4::new(p(&mut i)?, p(&mut i)?, p(&mut i)?, p(&mut i)?);
        if i.next().is_some() {
            Err(ParseIPv4Error)
        } else {
            Ok(addr)
        }
    }
}

impl fmt::Display for IPv4 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}.{}.{}.{}", self.a(), self.b(), self.c(), self.d(),)
    }
}

//
// CIDR prefix length
//

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct PrefixLength(u8);

#[derive(Clone, Debug, PartialEq)]
struct InvalidPrefixLengthError;

impl convert::TryFrom<u8> for PrefixLength {
    type Error = InvalidPrefixLengthError;

    fn try_from(x: u8) -> Result<Self, InvalidPrefixLengthError> {
        if x <= 32 {
            Ok(Self(x))
        } else {
            Err(InvalidPrefixLengthError)
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
struct ParsePrefixLengthError;

impl FromStr for PrefixLength {
    type Err = ParsePrefixLengthError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.parse::<u8>() {
            Ok(n) if n < 33 => Ok(Self(n)),
            _ => Err(ParsePrefixLengthError),
        }
    }
}

impl fmt::Display for PrefixLength {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

//
// Parsing and formatting
//

fn fetch_subnets() -> Result<Vec<Subnet>, Error> {
    use neli::{
        consts::{
            NlFamily, NlmF, Nlmsg, RtAddrFamily, RtScope, RtTable, Rta, Rtm,
            Rtn, Rtprot,
        },
        err::NlError,
        nl::Nlmsghdr,
        rtnl::{Rtattrs, Rtmsg},
        socket::NlSocket,
    };

    impl From<NlError> for Error {
        fn from(_: NlError) -> Self {
            return Error::NetlinkError;
        }
    }

    let mut socket = NlSocket::connect(NlFamily::Route, None, None, true)
        .map_err(|_| Error::NetlinkError)?;
    socket.send_nl({
        let len = None;
        let nl_type = Rtm::Getroute;
        let flags = vec![NlmF::Request, NlmF::Dump];
        let seq = None;
        let pid = None;
        let payload = Rtmsg {
            rtm_family: RtAddrFamily::Inet,
            rtm_dst_len: 0,
            rtm_src_len: 0,
            rtm_tos: 0,
            rtm_table: RtTable::Unspec,
            rtm_protocol: Rtprot::Unspec,
            rtm_scope: RtScope::Universe,
            rtm_type: Rtn::Unspec,
            rtm_flags: vec![],
            rtattrs: Rtattrs::empty(),
        };
        Nlmsghdr::new(len, nl_type, flags, seq, pid, payload)
    })?;

    let mut subnets = Vec::new();
    loop {
        let nl = match socket.recv_nl::<u16, Rtmsg>(None) {
            Ok(nl) => nl,
            // XXX(soija) Hmm, this is weird; on my machine this seem to
            //            signify the end of messages instead of
            //            `NL_MSG_DONE`.  Perhaps investigate this a bit.
            Err(NlError::Msg(_)) => break,
            e => e?,
        };
        match Nlmsg::from(nl.nl_type) {
            Nlmsg::Done => break,
            Nlmsg::Error => return Err(Error::NetlinkError),
            _ => (),
        }
        if let Rtm::Newroute = Rtm::from(nl.nl_type) {
            if nl.nl_payload.rtm_table == RtTable::Main {
                use std::convert::TryFrom;
                if let Some(dst_ipv4_tup) = nl
                    .nl_payload
                    .rtattrs
                    .iter()
                    .find(|a| a.rta_type == Rta::Dst)
                    .and_then(|a| <&[u8; 4]>::try_from(&a.rta_payload[..]).ok())
                {
                    subnets.push(Subnet::new(
                        dst_ipv4_tup.into(),
                        nl.nl_payload
                            .rtm_dst_len
                            .try_into()
                            .map_err(|_| Error::NetlinkError)?,
                    ));
                }
            }
        }
        if !nl.nl_flags.contains(&NlmF::Multi) {
            break;
        };
    }
    Ok(subnets)
}

#[derive(Debug)]
enum Error {
    NetlinkError,
}

//
// Tests
//

#[cfg(test)]
mod tests {
    use super::*;

    fn n(a: u8, b: u8, c: u8, d: u8, l: u8) -> Subnet {
        Subnet::new(IPv4::new(a, b, c, d), l.try_into().unwrap())
    }

    const A: u32 = 1 << 24;
    const B: u32 = 1 << 16;
    const C: u32 = 1 << 8;

    #[test]
    fn test_network_block_range() {
        assert_eq!(n(1, 2, 3, 4, 0).block_start().0, u32::MIN);
        assert_eq!(n(1, 2, 3, 4, 0).last().0, u32::MAX);
        assert_eq!(n(1, 2, 3, 4, 8).block_start().0, A);
        assert_eq!(n(1, 2, 3, 4, 8).last().0, 2 * A - 1);
        assert_eq!(n(1, 2, 3, 4, 12).block_start().0, A);
        assert_eq!(n(1, 2, 3, 4, 12).last().0, A + 16 * B - 1);
        assert_eq!(n(1, 2, 3, 4, 31).block_start().0, A + 2 * B + 3 * C + 4);
        assert_eq!(n(1, 2, 3, 4, 31).last().0, A + 2 * B + 3 * C + 5);
        assert_eq!(n(1, 2, 3, 4, 32).block_start().0, A + 2 * B + 3 * C + 4);
        assert_eq!(n(1, 2, 3, 4, 32).last().0, A + 2 * B + 3 * C + 4);
    }

    #[test]
    fn test_network_blocks_equality() {
        // obvious equalities
        assert_eq!(n(1, 2, 3, 4, 0), n(1, 2, 3, 4, 0));
        assert_eq!(n(1, 2, 3, 4, 16), n(1, 2, 3, 4, 16));
        assert_eq!(n(1, 2, 3, 4, 32), n(1, 2, 3, 4, 32));
        // non-equalitites
        assert_ne!(n(1, 2, 3, 4, 31), n(1, 2, 3, 5, 31));
        assert_ne!(n(1, 2, 3, 4, 0), n(1, 2, 3, 4, 1));
        assert_ne!(n(1, 2, 3, 4, 32), n(1, 2, 3, 5, 32));
    }

    macro_rules! assert_lt {
        ($left:expr, $right:expr) => {{
            match (&$left, &$right) {
                (left_val, right_val) => {
                    if !(*left_val < *right_val) {
                        panic!(
                            r#"assertion failed: `(left < right)`
   left: `{:?}`,
  right: `{:?}`"#,
                            &*left_val, &*right_val
                        )
                    }
                }
            }
        }};
    }

    macro_rules! assert_not_lt {
        ($left:expr, $right:expr) => {{
            match (&$left, &$right) {
                (left_val, right_val) => {
                    if (*left_val < *right_val) {
                        panic!(
                            r#"assertion failed: `(left < right)`
   left: `{:?}`,
  right: `{:?}`"#,
                            &*left_val, &*right_val
                        )
                    }
                }
            }
        }};
    }

    #[test]
    fn test_nonoverlapping_block_ordering() {
        assert_lt!(n(1, 2, 2, 128, 28), n(1, 2, 3, 0, 30));
        assert_lt!(n(1, 2, 3, 0, 30), n(1, 2, 3, 4, 32));
        assert_lt!(n(1, 2, 2, 128, 28), n(1, 2, 3, 4, 32));
        assert_not_lt!(n(1, 2, 3, 0, 30), n(1, 2, 2, 128, 28));
        assert_not_lt!(n(1, 2, 3, 4, 32), n(1, 2, 3, 0, 30));
        assert_not_lt!(n(1, 2, 3, 4, 32), n(1, 2, 2, 128, 28));
    }

    #[test]
    fn test_overlapping_block_ordering() {
        assert_not_lt!(n(1, 2, 3, 4, 30), n(1, 2, 3, 4, 30));
        assert_not_lt!(n(1, 2, 3, 4, 30), n(1, 2, 3, 4, 24));
        assert_not_lt!(n(1, 2, 3, 4, 24), n(1, 2, 3, 4, 30));
    }

    #[test]
    fn test_subnet_iteration() {
        // strict subnets
        assert_eq!(
            n(1, 2, 3, 4, 30)
                .subnets(32.try_into().unwrap())
                .collect::<Vec<_>>(),
            [
                n(1, 2, 3, 4, 32),
                n(1, 2, 3, 5, 32),
                n(1, 2, 3, 6, 32),
                n(1, 2, 3, 7, 32),
            ]
        );
        // Skip first two /31 blocks from the start of the /29 block, third is
        // a partial /31 block, and the last is a whole /31 block.
        assert_eq!(
            n(1, 2, 3, 5, 29)
                .subnets(31.try_into().unwrap())
                .collect::<Vec<_>>(),
            [n(1, 2, 3, 5, 31), n(1, 2, 3, 6, 31),]
        );
        // can iterate itself
        assert_eq!(
            n(1, 2, 3, 4, 30)
                .subnets(30.try_into().unwrap())
                .collect::<Vec<_>>(),
            [n(1, 2, 3, 4, 30)]
        );
        // cannot iterate networks larger than itself
        assert_eq!(
            n(1, 2, 3, 4, 30)
                .subnets(29.try_into().unwrap())
                .collect::<Vec<_>>(),
            []
        );
        // interesting special case
        assert_eq!(
            n(1, 2, 3, 4, 0).subnets(1.try_into().unwrap()).collect::<Vec<_>>(),
            [n(1, 2, 3, 4, 1), n(128, 0, 0, 0, 1)]
        );
    }

    #[test]
    fn test_subnet_parsing() {
        assert_eq!(
            "1.2.3.4/32".parse::<Subnet>().ok(),
            Some(n(1, 2, 3, 4, 32))
        );
        assert_eq!(
            "1.2.3.4/33".parse::<Subnet>().err(),
            Some(ParseSubnetError)
        );
    }
}
