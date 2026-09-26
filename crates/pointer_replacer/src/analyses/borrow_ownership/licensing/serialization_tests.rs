//! Metadata transport controls over one actual compiler construction.

use super::{graph_tests::with_facts, matched::MatchedTransport};

#[test]
fn t14_matched_json_round_trips_deterministically_and_rejects_duplicate_map_keys() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn make() -> *mut i32 { let p = malloc(4); p }
pub unsafe fn run() { let p = make(); free(p); }
"#,
        |facts| {
            let transport = MatchedTransport::build(facts);
            let bytes = transport
                .encode_json()
                .expect("T14 metadata encoding must be available");
            let decoded = MatchedTransport::decode_json(&bytes).expect("metadata-only decode");
            assert_eq!(
                decoded, transport,
                "all relation, proof, source, terminal and denial data must round-trip"
            );
            assert_eq!(decoded.encode_json().unwrap(), bytes);
            assert_eq!(
                MatchedTransport::build(facts).encode_json().unwrap(),
                bytes,
                "repeated construction from the same facts has deterministic metadata bytes"
            );
            let document: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
            assert!(document["denials"].is_array());
            for field in ["functions", "relations", "guard_aliases"] {
                let mut corrupted = document.clone();
                let pairs = corrupted[field]
                    .as_array_mut()
                    .expect("compound maps encode as ordered pairs");
                let duplicate = pairs
                    .first()
                    .expect("real fixture exercises this map")
                    .clone();
                pairs.push(duplicate);
                let bytes = serde_json::to_vec(&corrupted).unwrap();
                assert!(
                    MatchedTransport::decode_json(&bytes).is_err(),
                    "duplicate keys in {field} must not silently overwrite a record"
                );
            }
        },
    );
}

#[test]
fn t14_metadata_rebuild_without_predicate_asts_matches_ordinary_transport() {
    use std::collections::BTreeMap;

    use super::{
        super::execution_guard::{self, ExecutionRole},
        transport::CandidateGraph,
    };

    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn make() -> *mut i32 { let p = malloc(4); p }
pub unsafe fn run() { let p = make(); free(p); }
"#,
        |facts| {
            let ordinary = MatchedTransport::build(facts);
            let graph = CandidateGraph::build(facts);
            let aliases = ordinary.guard_aliases().clone();
            assert!(!facts.guards.is_empty() && !facts.ownership_asts.is_empty());
            assert!(
                !aliases.is_empty(),
                "the real endpoints require guard identity metadata"
            );

            let mut metadata = facts.clone();
            metadata.guards.clear();
            metadata.ownership_asts = rustc_index::IndexVec::new();
            let rebuilt = execution_guard::with_role(ExecutionRole::CacheOnly, || {
                MatchedTransport::build_metadata(&metadata, &aliases)
            })
            .expect("T14 must reconstruct from metadata without predicate ASTs");
            assert_eq!(
                rebuilt.encode_json().unwrap(),
                ordinary.encode_json().unwrap()
            );
            assert_eq!(
                execution_guard::with_role(ExecutionRole::CacheOnly, || {
                    CandidateGraph::build_metadata(&metadata, &aliases)
                })
                .expect("candidate metadata reconstruction"),
                graph,
            );
            assert!(
                metadata.guards.is_empty() && metadata.ownership_asts.is_empty(),
                "metadata reconstruction must not recreate predicate or ownership ASTs"
            );

            if let Ok(incomplete) = execution_guard::with_role(ExecutionRole::CacheOnly, || {
                CandidateGraph::build_metadata(&metadata, &BTreeMap::new())
            }) {
                assert!(
                    incomplete.sources.is_empty() && incomplete.sinks.is_empty(),
                    "missing endpoint guard metadata must remain held"
                );
                assert!(incomplete.forward().is_empty());
            }
            if let Ok(incomplete) = execution_guard::with_role(ExecutionRole::CacheOnly, || {
                MatchedTransport::build_metadata(&metadata, &BTreeMap::new())
            }) {
                for sink in &graph.sinks {
                    assert!(incomplete.sources_for(sink.node).is_empty());
                    assert!(
                        incomplete.meets_for(sink.node).is_empty(),
                        "missing guards cannot silently become an unguarded meet"
                    );
                }
            }
        },
    );
}

#[test]
fn t14_frozen_transport_is_normative_and_snapshot_validation_is_ast_free() {
    use super::{
        super::execution_guard::{self, ExecutionRole},
        recursive,
        snapshot::Snapshot,
    };
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn make(n: usize) -> *mut i32 { if n == 0 { malloc(4) } else { make(n-1) } }
pub unsafe fn run() { let p = make(1); free(p); }
"#,
        |facts| {
            let frozen = facts
                .licensing
                .as_ref()
                .expect("completed normative transport must exist without optional export");
            assert_eq!(frozen.matched, MatchedTransport::build(facts));
            assert!(
                frozen
                    .recursive
                    .iter()
                    .any(|(construction, function, certificate)| {
                        *construction == 0
                            && function == "make"
                            && *certificate == recursive::certify_invocations(facts, 0, "make")
                    })
            );
            let snapshot =
                Snapshot::capture(facts, 3).expect("snapshot of already produced transport");
            assert_eq!(snapshot.offset, 3);
            let metadata = snapshot.metadata.facts();
            assert!(
                metadata.guards.is_empty()
                    && metadata.ownership_asts.is_empty()
                    && metadata.licensing.is_none()
            );
            execution_guard::with_role(ExecutionRole::CacheOnly, || snapshot.validate())
                .expect("complete AST-free snapshot validation");
        },
    );
}
