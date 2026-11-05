use super::cursor::index::{IndexError, IndexOp};

#[test]
fn w02_backward_step_keeps_prefix() {
    let saved = 3;
    let advanced = IndexOp::Add(2).apply(saved, 8).unwrap();
    assert_eq!(IndexOp::Offset(-4).apply(advanced, 8), Ok(1));
    assert_eq!(saved, 3, "local copies retain independent indices");
}

#[test]
fn w03_endpoint_and_backedge_indices() {
    let mut index = 0;
    while index != 8 {
        index = IndexOp::Add(1).apply(index, 8).unwrap();
    }
    assert_eq!(index, 8, "the one-past position is representable");
    while index != 0 {
        index = IndexOp::Sub(1).apply(index, 8).unwrap();
    }
    assert_eq!(IndexOp::Add(1).apply(8, 8), Err(IndexError::OutsideWindow));
}

#[test]
fn w04_signed_minimum_and_unsigned_width() {
    let magnitude = isize::MIN.unsigned_abs();
    assert_eq!(
        IndexOp::Offset(isize::MIN).apply(magnitude, usize::MAX),
        Ok(0)
    );
    assert_eq!(
        IndexOp::Add(usize::MAX).apply(0, usize::MAX),
        Ok(usize::MAX)
    );
    assert_eq!(
        IndexOp::Sub(usize::MAX).apply(usize::MAX, usize::MAX),
        Ok(0)
    );
    assert_eq!(
        IndexOp::Add(1).apply(usize::MAX, usize::MAX),
        Err(IndexError::Overflow)
    );
    assert_eq!(IndexOp::Sub(1).apply(0, 8), Err(IndexError::Overflow));
    assert_eq!(IndexOp::Offset(-1).apply(0, 8), Err(IndexError::Overflow));
}

#[test]
fn w04_small_domain_matches_integer_reference() {
    for length in 0..=12 {
        for index in 0..=length {
            for delta in -15..=15 {
                let expected = index as i128 + delta as i128;
                let actual = IndexOp::Offset(delta).apply(index, length);
                if (0..=length as i128).contains(&expected) {
                    assert_eq!(actual, Ok(expected as usize));
                } else {
                    assert!(actual.is_err());
                }
            }
        }
    }
    assert_eq!(
        IndexOp::Sub(1).apply(9, 8),
        Err(IndexError::OutsideWindow),
        "an invalid incoming position cannot be repaired by stepping into range"
    );
}
