use std::collections::{BTreeMap, BTreeSet};

const COUNT_SENTINEL: &str = "A5P1 ";

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FormalKey {
    function: String,
    parameter: u32,
    depth: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FormalDecision {
    key: FormalKey,
    settles_ref: bool,
    currently_predicted_ref: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
enum SetPairEvidence {
    #[default]
    Unknown,
    Complete {
        left: BTreeSet<String>,
        right: BTreeSet<String>,
    },
    Incomplete {
        left: BTreeSet<String>,
        right: BTreeSet<String>,
    },
}

impl SetPairEvidence {
    fn proves_disjoint(&self) -> bool {
        let Self::Complete { left, right } = self else {
            return false;
        };
        !left.is_empty() && !right.is_empty() && left.is_disjoint(right)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct PairFacts {
    storage_alias: bool,
    projection_disjoint: bool,
    origins: SetPairEvidence,
    points_to: SetPairEvidence,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PairClass {
    ProvenDisjoint,
    NotProvenDisjoint,
}

fn classify_pair(facts: &PairFacts) -> PairClass {
    if facts.storage_alias {
        return PairClass::NotProvenDisjoint;
    }
    if facts.projection_disjoint
        || facts.origins.proves_disjoint()
        || facts.points_to.proves_disjoint()
    {
        PairClass::ProvenDisjoint
    } else {
        PairClass::NotProvenDisjoint
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CallSite {
    id: String,
    arguments: Vec<FormalDecision>,
    pair_facts: BTreeMap<(usize, usize), PairFacts>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct FunctionNode {
    unknown_caller_root: bool,
    callees: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProgramInput {
    name: String,
    call_sites: Vec<CallSite>,
    functions: BTreeMap<String, FunctionNode>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProgramCounts {
    program: String,
    sites_with_two_ref_args: usize,
    sites_not_proven_disjoint: usize,
    attributed_predicted_refs: usize,
    attributed_predicted_refs_depth0: usize,
    unknown_caller_reachable: usize,
    local_functions: usize,
}

impl ProgramCounts {
    fn validate(&self) -> Result<(), String> {
        if self.program.is_empty() || self.program.chars().any(char::is_whitespace) {
            return Err("program must be a non-empty whitespace-free key".to_owned());
        }
        if self.sites_not_proven_disjoint > self.sites_with_two_ref_args {
            return Err("count 2 exceeds count 1".to_owned());
        }
        if self.attributed_predicted_refs_depth0 > self.attributed_predicted_refs {
            return Err("depth-0 count exceeds the all-depth count".to_owned());
        }
        if self.unknown_caller_reachable > self.local_functions {
            return Err("call-graph numerator exceeds its denominator".to_owned());
        }
        Ok(())
    }
}

fn measure_program(input: &ProgramInput) -> Result<ProgramCounts, String> {
    let mut site_ids = BTreeSet::new();
    let mut sites_with_two_ref_args = 0usize;
    let mut sites_not_proven_disjoint = 0usize;
    let mut attributed = BTreeSet::new();

    for site in &input.call_sites {
        if !site_ids.insert(site.id.as_str()) {
            return Err(format!("duplicate call-site id `{}`", site.id));
        }
        let ref_args = site
            .arguments
            .iter()
            .enumerate()
            .filter_map(|(index, formal)| formal.settles_ref.then_some(index))
            .collect::<Vec<_>>();
        if ref_args.len() < 2 {
            continue;
        }
        sites_with_two_ref_args += 1;

        let mut risky = false;
        for (offset, &left) in ref_args.iter().enumerate() {
            for &right in &ref_args[offset + 1..] {
                let facts = site
                    .pair_facts
                    .get(&(left, right))
                    .cloned()
                    .unwrap_or_default();
                if classify_pair(&facts) == PairClass::NotProvenDisjoint {
                    risky = true;
                    for index in [left, right] {
                        let formal = &site.arguments[index];
                        if formal.currently_predicted_ref {
                            attributed.insert(formal.key.clone());
                        }
                    }
                }
            }
        }
        sites_not_proven_disjoint += usize::from(risky);
    }

    let mut reachable = BTreeSet::new();
    let mut pending = input
        .functions
        .iter()
        .filter_map(|(name, node)| node.unknown_caller_root.then_some(name.clone()))
        .collect::<Vec<_>>();
    while let Some(function) = pending.pop() {
        if !reachable.insert(function.clone()) {
            continue;
        }
        let Some(node) = input.functions.get(&function) else {
            return Err(format!(
                "call graph references unknown local function `{function}`"
            ));
        };
        for callee in &node.callees {
            if !input.functions.contains_key(callee) {
                return Err(format!(
                    "call graph references unknown local callee `{callee}`"
                ));
            }
            pending.push(callee.clone());
        }
    }

    let counts = ProgramCounts {
        program: input.name.clone(),
        sites_with_two_ref_args,
        sites_not_proven_disjoint,
        attributed_predicted_refs: attributed.len(),
        attributed_predicted_refs_depth0: attributed.iter().filter(|key| key.depth == 0).count(),
        unknown_caller_reachable: reachable.len(),
        local_functions: input.functions.len(),
    };
    counts.validate()?;
    Ok(counts)
}

fn render_count_line(counts: &ProgramCounts) -> String {
    counts
        .validate()
        .expect("only valid P1 counts may be rendered");
    format!(
        "{COUNT_SENTINEL}program={} c1={} c2={} c3={} c3_depth0={} cg_num={} cg_den={}",
        counts.program,
        counts.sites_with_two_ref_args,
        counts.sites_not_proven_disjoint,
        counts.attributed_predicted_refs,
        counts.attributed_predicted_refs_depth0,
        counts.unknown_caller_reachable,
        counts.local_functions,
    )
}

fn parse_count_line(line: &str) -> Result<ProgramCounts, String> {
    let body = line
        .trim()
        .strip_prefix(COUNT_SENTINEL)
        .ok_or_else(|| "missing A5P1 sentinel".to_owned())?;
    let mut fields = BTreeMap::new();
    for token in body.split_whitespace() {
        let (key, value) = token
            .split_once('=')
            .ok_or_else(|| format!("malformed token `{token}`"))?;
        if fields.insert(key, value).is_some() {
            return Err(format!("duplicate field `{key}`"));
        }
    }
    const EXPECTED: [&str; 7] = ["program", "c1", "c2", "c3", "c3_depth0", "cg_num", "cg_den"];
    if fields.len() != EXPECTED.len() || EXPECTED.iter().any(|key| !fields.contains_key(key)) {
        return Err("count row does not contain the exact P1 schema".to_owned());
    }
    let number = |key: &str| -> Result<usize, String> {
        fields[key]
            .parse::<usize>()
            .map_err(|error| format!("invalid `{key}`: {error}"))
    };
    let counts = ProgramCounts {
        program: fields["program"].to_owned(),
        sites_with_two_ref_args: number("c1")?,
        sites_not_proven_disjoint: number("c2")?,
        attributed_predicted_refs: number("c3")?,
        attributed_predicted_refs_depth0: number("c3_depth0")?,
        unknown_caller_reachable: number("cg_num")?,
        local_functions: number("cg_den")?,
    };
    counts.validate()?;
    Ok(counts)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::*;

    fn set(values: &[&str]) -> BTreeSet<String> {
        values.iter().map(|value| (*value).to_owned()).collect()
    }

    fn formal(function: &str, parameter: u32, depth: u8) -> FormalDecision {
        FormalDecision {
            key: FormalKey {
                function: function.to_owned(),
                parameter,
                depth,
            },
            settles_ref: true,
            currently_predicted_ref: true,
        }
    }

    #[test]
    fn absence_of_storage_alias_is_unknown_not_disjoint() {
        let facts = PairFacts {
            storage_alias: false,
            ..PairFacts::default()
        };

        assert_eq!(classify_pair(&facts), PairClass::NotProvenDisjoint);
    }

    #[test]
    fn only_complete_positive_evidence_proves_disjointness() {
        let projection_disjoint = PairFacts {
            projection_disjoint: true,
            ..PairFacts::default()
        };
        let complete_disjoint_origins = PairFacts {
            origins: SetPairEvidence::Complete {
                left: set(&["origin-a"]),
                right: set(&["origin-b"]),
            },
            ..PairFacts::default()
        };
        let complete_disjoint_points_to = PairFacts {
            points_to: SetPairEvidence::Complete {
                left: set(&["alloc-a"]),
                right: set(&["alloc-b"]),
            },
            ..PairFacts::default()
        };
        let incomplete_disjoint = PairFacts {
            points_to: SetPairEvidence::Incomplete {
                left: set(&["alloc-a"]),
                right: set(&["alloc-b"]),
            },
            ..PairFacts::default()
        };
        let known_storage_alias = PairFacts {
            storage_alias: true,
            projection_disjoint: true,
            ..PairFacts::default()
        };

        assert_eq!(
            classify_pair(&projection_disjoint),
            PairClass::ProvenDisjoint
        );
        assert_eq!(
            classify_pair(&complete_disjoint_origins),
            PairClass::ProvenDisjoint
        );
        assert_eq!(
            classify_pair(&complete_disjoint_points_to),
            PairClass::ProvenDisjoint
        );
        assert_eq!(
            classify_pair(&incomplete_disjoint),
            PairClass::NotProvenDisjoint
        );
        assert_eq!(
            classify_pair(&known_storage_alias),
            PairClass::NotProvenDisjoint
        );
    }

    #[test]
    fn risky_sites_deduplicate_formals_and_report_the_depth_zero_subset() {
        let outer = formal("callee", 1, 0);
        let deeper = formal("callee", 2, 1);
        let mut pair_facts = BTreeMap::new();
        pair_facts.insert((0, 1), PairFacts::default());
        let site = CallSite {
            id: "caller:bb0".to_owned(),
            arguments: vec![outer.clone(), deeper.clone()],
            pair_facts,
        };
        let one_ref_site = CallSite {
            id: "caller:bb2".to_owned(),
            arguments: vec![formal("callee", 3, 0)],
            pair_facts: BTreeMap::new(),
        };
        let program = ProgramInput {
            name: "fixture".to_owned(),
            call_sites: vec![
                site.clone(),
                CallSite {
                    id: "caller:bb1".to_owned(),
                    ..site
                },
                one_ref_site,
            ],
            functions: BTreeMap::new(),
        };

        let measured = measure_program(&program).expect("valid fixture");

        assert_eq!(measured.sites_with_two_ref_args, 2);
        assert_eq!(measured.sites_not_proven_disjoint, 2);
        assert_eq!(measured.attributed_predicted_refs, 2);
        assert_eq!(measured.attributed_predicted_refs_depth0, 1);
    }

    #[test]
    fn closedness_is_the_forward_closure_of_unknown_caller_roots() {
        let functions = BTreeMap::from([
            (
                "root".to_owned(),
                FunctionNode {
                    unknown_caller_root: true,
                    callees: set(&["mid"]),
                },
            ),
            (
                "mid".to_owned(),
                FunctionNode {
                    unknown_caller_root: false,
                    callees: set(&["leaf"]),
                },
            ),
            ("leaf".to_owned(), FunctionNode::default()),
            ("closed".to_owned(), FunctionNode::default()),
        ]);
        let program = ProgramInput {
            name: "fixture".to_owned(),
            call_sites: Vec::new(),
            functions,
        };

        let measured = measure_program(&program).expect("valid fixture");

        assert_eq!(measured.unknown_caller_reachable, 3);
        assert_eq!(measured.local_functions, 4);
    }

    #[test]
    fn raw_count_rows_round_trip_and_missing_fields_fail_closed() {
        let counts = ProgramCounts {
            program: "fixture".to_owned(),
            sites_with_two_ref_args: 7,
            sites_not_proven_disjoint: 5,
            attributed_predicted_refs: 4,
            attributed_predicted_refs_depth0: 3,
            unknown_caller_reachable: 2,
            local_functions: 6,
        };
        let encoded = render_count_line(&counts);

        assert_eq!(parse_count_line(&encoded), Ok(counts));
        assert!(parse_count_line("A5P1 program=fixture c1=7").is_err());
        assert!(
            parse_count_line(
                "A5P1 program=fixture program=fixture c1=7 c2=5 c3=4 c3_depth0=3 cg_num=2 cg_den=6"
            )
            .is_err()
        );
        assert!(
            parse_count_line("A5P1 program=fixture c1=1 c2=2 c3=4 c3_depth0=3 cg_num=2 cg_den=6")
                .is_err()
        );
    }
}
