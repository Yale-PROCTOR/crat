//! Relay main/388 (R1356-1), 3d: the `Unknown`-atom lookup equals the scan it replaces, on a fixture
//! covering a port that matches by `def_start`, one by `use_start`, one by both, one with no match,
//! loads at points with several consume rows, a consume row in another construction, a `Missing`
//! window, and consume rows with a `None` point component that must not match.
use super::{
    super::super::{
        export::ProjKey,
        ownership_access::PlaceSyntax,
        ownership_evidence::Point,
        ownership_occurrence::{Availability, Consumption, SourceSpan, Window},
    },
    *,
};

fn consume(
    construction: u32,
    function: Option<&str>,
    block: Option<u32>,
    statement: Option<usize>,
    window: Option<(u32, u32)>,
) -> Consumption {
    let projected = match window {
        Some((use_start, def_start)) => Availability::Present(Window {
            use_start,
            use_end: use_start + 1,
            def_start,
            def_end: def_start + 1,
        }),
        None => Availability::Missing("fixture".to_owned()),
    };
    Consumption {
        point: Point {
            construction,
            function: function.map(str::to_owned),
            phase: "statement".to_owned(),
            block,
            statement,
        },
        ordinal: 0,
        span: SourceSpan {
            file: "fixture.rs".to_owned(),
            lo: 0,
            hi: 0,
        },
        local: 1,
        projection: vec![ProjKey::Deref],
        ssa_use: None,
        ssa_def: None,
        base: Availability::Missing("fixture".to_owned()),
        projected,
        pointer_paths: Availability::Missing("fixture".to_owned()),
    }
}

fn load(function: &str, block: u32, statement: usize, field_key: &str) -> Load {
    Load {
        site: Site {
            function: function.to_owned(),
            block,
            statement,
            field_key: field_key.to_owned(),
            place: PlaceSyntax {
                local: 1,
                projection: vec![ProjKey::Deref, ProjKey::Field(0)],
            },
        },
        shared_reference_root: false,
        direct_projection: true,
    }
}

fn fixture() -> Facts {
    let mut facts = Facts::default();
    facts.consumes = vec![
        // f bb0[1]: two rows -- (use 10, def 20) and (use 30, def 10).
        consume(0, Some("f"), Some(0), Some(1), Some((10, 20))),
        consume(0, Some("f"), Some(0), Some(1), Some((30, 10))),
        // f bb2[0]: one row, in construction 1 too.
        consume(0, Some("f"), Some(2), Some(0), Some((40, 41))),
        consume(1, Some("f"), Some(2), Some(0), Some((10, 50))),
        // g bb1[3]: a Missing window.
        consume(0, Some("g"), Some(1), Some(3), None),
        // A row with a None component at each position, at g bb1[3]'s point: never matched.
        consume(0, None, Some(1), Some(3), Some((60, 61))),
        consume(0, Some("g"), None, Some(3), Some((62, 63))),
        consume(0, Some("g"), Some(1), None, Some((64, 65))),
        // h bb0[0]: same var as a def and as a use.
        consume(0, Some("h"), Some(0), Some(0), Some((70, 70))),
    ];
    facts.field_support_inputs.loads = vec![
        load("f", 0, 1, "S::field0@d0"),
        load("f", 2, 0, "S::field1@d0"),
        load("g", 1, 3, "T::field0@d0"),
        load("h", 0, 0, "U::field2@d0"),
        load("h", 0, 0, "U::field3@d0"),
        // A load at a point with no consume row.
        load("k", 9, 9, "V::field0@d0"),
    ];
    facts
}

/// Every port the fixture names, and some it does not: the lookup equals the scan at each.
#[test]
fn r1356_3d_the_lookup_equals_the_scan() {
    let facts = fixture();
    let ports = loads_by_port(&facts);
    let mut nonempty = 0;
    for construction in 0..=2 {
        for var in (0..=80).chain([u32::MAX]) {
            let port = Node { construction, var };
            let scanned = loads_by_scan(&facts, port);
            let looked = ports.get(&(construction, var)).cloned().unwrap_or_default();
            assert_eq!(looked, scanned, "port {port:?}");
            nonempty += usize::from(!scanned.is_empty());
        }
    }
    // Construction 0: 10, 20, 30, 40, 41, 70; construction 1: 10, 50. No match elsewhere.
    assert_eq!(nonempty, 8, "the fixture's matching ports");
}

/// The cases by name: a def match, a use match, a var that is both, several rows at one point, the
/// construction kept apart, and the `None` components and the `Missing` window never matching.
#[test]
fn r1356_3d_the_cases() {
    let facts = fixture();
    let ports = loads_by_port(&facts);
    let get = |construction, var| ports.get(&(construction, var)).cloned().unwrap_or_default();
    let keys = |keys: &[&str]| {
        keys.iter()
            .map(|key| (*key).to_owned())
            .collect::<BTreeSet<_>>()
    };
    assert_eq!(get(0, 20), keys(&["S::field0@d0"]), "by def_start");
    assert_eq!(get(0, 30), keys(&["S::field0@d0"]), "by use_start");
    assert_eq!(
        get(0, 10),
        keys(&["S::field0@d0"]),
        "use of one row, def of another"
    );
    assert_eq!(get(0, 70), keys(&["U::field2@d0", "U::field3@d0"]), "both");
    assert_eq!(get(1, 10), keys(&["S::field1@d0"]), "construction 1");
    assert_eq!(
        get(1, 40),
        keys(&[]),
        "construction 0's row is not construction 1's"
    );
    for var in 60..=65 {
        assert_eq!(
            get(0, var),
            keys(&[]),
            "a None point component never matches"
        );
    }
    assert_eq!(get(0, 99), keys(&[]), "no match: Unknown");
}
