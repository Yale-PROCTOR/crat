use super::cursor::carrier::{Coordinates, Extent, ExtentOrigin, Hold, Position, SignCapture};

fn position(index: usize) -> Position<u32> {
    Position {
        coordinates: Coordinates {
            origin: 1,
            generation_relation: 2,
            window_origin: 3,
            element_type: 4,
            element_size: 4,
        },
        index,
        length: 8,
    }
}

#[test]
fn w01_raw_sign_capture_does_not_manufacture_a_three_way_verdict() {
    assert_eq!(
        SignCapture::from(Some(true)),
        SignCapture::NegativeOrUnknown
    );
    assert_eq!(SignCapture::from(Some(false)), SignCapture::Nonnegative);
    assert_eq!(SignCapture::from(None), SignCapture::Missing);
}

#[test]
fn w05_distance_requires_same_generation_window_and_layout() {
    let p = position(5);
    let q = position(2);
    assert_eq!(p.difference(&q), Ok(3));
    assert_eq!(q.difference(&p), Ok(-3));
    for changed in [
        Coordinates {
            origin: 9,
            ..q.coordinates
        },
        Coordinates {
            generation_relation: 9,
            ..q.coordinates
        },
        Coordinates {
            window_origin: 9,
            ..q.coordinates
        },
        Coordinates {
            element_type: 9,
            ..q.coordinates
        },
        Coordinates {
            element_size: 8,
            ..q.coordinates
        },
    ] {
        assert_eq!(
            p.difference(&Position {
                coordinates: changed,
                ..q
            }),
            Err(Hold::Origin)
        );
    }
    let zst = Position {
        coordinates: Coordinates {
            element_size: 0,
            ..p.coordinates
        },
        ..p
    };
    assert_eq!(zst.difference(&zst), Err(Hold::Layout));
    let oversized = Position {
        length: usize::MAX,
        ..p
    };
    assert_eq!(oversized.difference(&oversized), Err(Hold::Layout));
}

#[test]
fn w03_endpoint_has_no_element_reference() {
    assert_eq!(position(7).element_index(), Ok(7));
    assert_eq!(position(8).element_index(), Err(Hold::Window));
    assert_eq!(position(8).difference(&position(0)), Ok(8));
    assert_eq!(position(9).difference(&position(0)), Err(Hold::Window));
}

#[test]
fn w06_w08_optional_indices_copy_without_a_base_capability() {
    let original = Some(position(3));
    let mut copy = original;
    copy.as_mut().unwrap().index = 5;
    assert_eq!(original.unwrap().index, 3);
    assert_eq!(copy.unwrap().difference(&original.unwrap()), Ok(2));
    let absent: Option<Position<u32>> = None;
    assert!(absent.is_none(), "null is absence, not position zero");
}

#[test]
fn w07_tail_preserves_fallback_origin_and_gets_a_site_receipt() {
    let base = Extent {
        elements: 1024,
        origin: ExtentOrigin::Fallback {
            origin_receipt: 10,
            site_receipt: 10,
        },
    };
    let tail = base.tail(8, 11).unwrap().tail(4, 12).unwrap();
    assert_eq!(
        tail,
        Extent {
            elements: 1012,
            origin: ExtentOrigin::Fallback {
                origin_receipt: 10,
                site_receipt: 12
            },
        }
    );
    let exact = Extent {
        elements: 8,
        origin: ExtentOrigin::Evidence(20),
    };
    assert_eq!(
        exact.tail(3, 21),
        Ok(Extent {
            elements: 5,
            origin: ExtentOrigin::Evidence(20)
        })
    );
    assert_eq!(exact.tail(9, 21), Err(Hold::Window));
}
