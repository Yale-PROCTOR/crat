use std::collections::{BTreeMap, BTreeSet, HashMap};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Expr {
    True,
    False,
    Lit {
        coord: usize,
        values: BTreeSet<usize>,
    },
    Not(Box<Expr>),
    And(Vec<Expr>),
    Or(Vec<Expr>),
}

#[derive(Clone, Debug)]
pub(crate) struct Universe {
    domain_sizes: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct MemoKey {
    coords: Vec<usize>,
    bits: Vec<u64>,
    allow_complement: bool,
}

pub(crate) struct Solver<'a> {
    universe: &'a Universe,
    memo: HashMap<MemoKey, Expr>,
}

impl Universe {
    pub(crate) fn new(domain_sizes: Vec<usize>) -> Self {
        for &size in &domain_sizes {
            assert!(size > 0, "each coordinate domain must be non-empty");
        }
        Self { domain_sizes }
    }

    pub(crate) fn coordinate_count(&self) -> usize {
        self.domain_sizes.len()
    }

    pub(crate) fn all_coordinates(&self) -> Vec<usize> {
        (0..self.coordinate_count()).collect()
    }

    pub(crate) fn domain_size(&self, coords: &[usize]) -> usize {
        coords.iter().fold(1usize, |acc, &coord| {
            acc.saturating_mul(self.domain_sizes[coord])
        })
    }

    pub(crate) fn empty_bits(&self, coords: &[usize]) -> Vec<u64> {
        vec![0; word_len(self.domain_size(coords))]
    }

    pub(crate) fn full_bits(&self, coords: &[usize]) -> Vec<u64> {
        let size = self.domain_size(coords);
        let mut bits = vec![!0u64; word_len(size)];
        clear_unused_tail_bits(&mut bits, size);
        bits
    }

    pub(crate) fn tuple_index(&self, coords: &[usize], tuple: &[usize]) -> usize {
        assert_eq!(coords.len(), tuple.len());
        let mut index = 0usize;
        for (&coord, &value) in coords.iter().zip(tuple) {
            assert!(value < self.domain_sizes[coord]);
            index = index * self.domain_sizes[coord] + value;
        }
        index
    }

    pub(crate) fn set_tuple_bit(&self, coords: &[usize], bits: &mut [u64], tuple: &[usize]) {
        let index = self.tuple_index(coords, tuple);
        set_bit(bits, index);
    }

    pub(crate) fn expr_size(&self, expr: &Expr) -> usize {
        match expr {
            Expr::True | Expr::False => 1,
            Expr::Lit { coord, values } => self.literal_cost(*coord, values),
            Expr::Not(expr) => 1 + self.expr_size(expr),
            Expr::And(args) | Expr::Or(args) => {
                1 + args.iter().map(|arg| self.expr_size(arg)).sum::<usize>()
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn evaluate(&self, expr: &Expr, tuple: &[usize]) -> bool {
        match expr {
            Expr::True => true,
            Expr::False => false,
            Expr::Lit { coord, values } => values.contains(&tuple[*coord]),
            Expr::Not(expr) => !self.evaluate(expr, tuple),
            Expr::And(args) => args.iter().all(|arg| self.evaluate(arg, tuple)),
            Expr::Or(args) => args.iter().any(|arg| self.evaluate(arg, tuple)),
        }
    }

    fn literal_cost(&self, coord: usize, values: &BTreeSet<usize>) -> usize {
        if values.is_empty() || values.len() == self.domain_sizes[coord] || values.len() == 1 {
            return 1;
        }

        let positive_cost = values.len() + 1;
        let excluded = self.domain_sizes[coord] - values.len();
        let negative_cost = match excluded {
            0 => 1,
            1 => 2,
            _ => excluded + 2,
        };
        positive_cost.min(negative_cost)
    }

    fn canonical_expr_string(expr: &Expr) -> String {
        match expr {
            Expr::True => "T".to_string(),
            Expr::False => "F".to_string(),
            Expr::Lit { coord, values } => {
                let values = values
                    .iter()
                    .map(usize::to_string)
                    .collect::<Vec<_>>()
                    .join(",");
                format!("L{coord}[{values}]")
            }
            Expr::Not(expr) => format!("!{}", Self::canonical_expr_string(expr)),
            Expr::And(args) => {
                let args = args
                    .iter()
                    .map(Self::canonical_expr_string)
                    .collect::<Vec<_>>()
                    .join("&");
                format!("A({args})")
            }
            Expr::Or(args) => {
                let args = args
                    .iter()
                    .map(Self::canonical_expr_string)
                    .collect::<Vec<_>>()
                    .join("|");
                format!("O({args})")
            }
        }
    }
}

impl<'a> Solver<'a> {
    pub(crate) fn new(universe: &'a Universe) -> Self {
        Self {
            universe,
            memo: HashMap::new(),
        }
    }

    pub(crate) fn solve(&mut self, target: Vec<u64>) -> Expr {
        let coords = self.universe.all_coordinates();
        self.solve_subproblem(&coords, target, true)
    }

    fn solve_subproblem(
        &mut self,
        coords: &[usize],
        bits: Vec<u64>,
        allow_complement: bool,
    ) -> Expr {
        let key = MemoKey {
            coords: coords.to_vec(),
            bits: bits.clone(),
            allow_complement,
        };
        if let Some(expr) = self.memo.get(&key) {
            return expr.clone();
        }

        let domain_size = self.universe.domain_size(coords);
        let full_bits = self.universe.full_bits(coords);
        let expr = if is_empty(&bits) {
            Expr::False
        } else if bits == full_bits {
            Expr::True
        } else if coords.len() == 1 {
            let values = values_from_bits(&bits, self.universe.domain_sizes[coords[0]]);
            self.simplify(Expr::Lit {
                coord: coords[0],
                values,
            })
        } else {
            let mut best_expr = None::<Expr>;
            let mut best_size = usize::MAX;

            for (pivot_pos, &pivot_coord) in coords.iter().enumerate() {
                let candidate =
                    self.build_decomposition_candidate(coords, &bits, pivot_pos, pivot_coord);
                self.consider_candidate(candidate, &mut best_expr, &mut best_size);
            }

            if allow_complement {
                let complement = complement_bits(&bits, domain_size);
                let inner = self.solve_subproblem(coords, complement, false);
                let candidate = self.simplify(Expr::Not(Box::new(inner)));
                self.consider_candidate(candidate, &mut best_expr, &mut best_size);
            }

            best_expr.expect("non-trivial problem must have a candidate")
        };

        self.memo.insert(key, expr.clone());
        expr
    }

    fn consider_candidate(
        &self,
        candidate: Expr,
        best_expr: &mut Option<Expr>,
        best_size: &mut usize,
    ) {
        let candidate_size = self.universe.expr_size(&candidate);
        let should_replace = match best_expr {
            None => true,
            Some(_) if candidate_size < *best_size => true,
            Some(existing) if candidate_size == *best_size => {
                Universe::canonical_expr_string(&candidate)
                    < Universe::canonical_expr_string(existing)
            }
            Some(_) => false,
        };

        if should_replace {
            *best_size = candidate_size;
            *best_expr = Some(candidate);
        }
    }

    fn build_decomposition_candidate(
        &mut self,
        coords: &[usize],
        bits: &[u64],
        pivot_pos: usize,
        pivot_coord: usize,
    ) -> Expr {
        let rest_coords = remove_at(coords, pivot_pos);
        let full_rest = self.universe.full_bits(&rest_coords);
        let pivot_domain_size = self.universe.domain_sizes[pivot_coord];
        let mut groups = BTreeMap::<Vec<u64>, BTreeSet<usize>>::new();

        for value in 0..pivot_domain_size {
            let cofactor = self.compute_cofactor(coords, bits, pivot_pos, value);
            groups.entry(cofactor).or_default().insert(value);
        }

        let mut terms = Vec::new();
        for (cofactor, values) in groups {
            if is_empty(&cofactor) {
                continue;
            }

            let lit = Expr::Lit {
                coord: pivot_coord,
                values,
            };
            let term = if cofactor == full_rest {
                lit
            } else {
                let sub = self.solve_subproblem(&rest_coords, cofactor, true);
                Expr::And(vec![lit, sub])
            };
            terms.push(term);
        }

        if terms.is_empty() {
            Expr::False
        } else if terms.len() == 1 {
            self.simplify(terms.pop().unwrap())
        } else {
            self.simplify(Expr::Or(terms))
        }
    }

    fn compute_cofactor(
        &self,
        coords: &[usize],
        bits: &[u64],
        pivot_pos: usize,
        pivot_value: usize,
    ) -> Vec<u64> {
        let rest_coords = remove_at(coords, pivot_pos);
        let rest_domain_size = self.universe.domain_size(&rest_coords);
        let mut cofactor = vec![0; word_len(rest_domain_size)];

        for rest_index in 0..rest_domain_size {
            let full_index =
                self.extend_index(&rest_coords, rest_index, pivot_pos, coords, pivot_value);
            if get_bit(bits, full_index) {
                set_bit(&mut cofactor, rest_index);
            }
        }

        cofactor
    }

    fn extend_index(
        &self,
        rest_coords: &[usize],
        rest_index: usize,
        pivot_pos: usize,
        coords: &[usize],
        pivot_value: usize,
    ) -> usize {
        let rest_tuple = self.decode_tuple(rest_coords, rest_index);
        let mut full_tuple = Vec::with_capacity(coords.len());
        let mut rest_iter = rest_tuple.into_iter();
        for position in 0..coords.len() {
            if position == pivot_pos {
                full_tuple.push(pivot_value);
            } else {
                full_tuple.push(rest_iter.next().unwrap());
            }
        }
        self.universe.tuple_index(coords, &full_tuple)
    }

    fn decode_tuple(&self, coords: &[usize], mut index: usize) -> Vec<usize> {
        if coords.is_empty() {
            return Vec::new();
        }

        let mut tuple = vec![0; coords.len()];
        for pos in (0..coords.len()).rev() {
            let radix = self.universe.domain_sizes[coords[pos]];
            tuple[pos] = index % radix;
            index /= radix;
        }
        tuple
    }

    fn simplify(&self, expr: Expr) -> Expr {
        let mut current = expr;
        loop {
            let next = self.simplify_one_pass(current.clone());
            if next == current {
                return next;
            }
            current = next;
        }
    }

    fn simplify_one_pass(&self, expr: Expr) -> Expr {
        match expr {
            Expr::True => Expr::True,
            Expr::False => Expr::False,
            Expr::Lit { coord, values } => {
                if values.is_empty() {
                    Expr::False
                } else if values.len() == self.universe.domain_sizes[coord] {
                    Expr::True
                } else {
                    Expr::Lit { coord, values }
                }
            }
            Expr::Not(expr) => {
                let expr = self.simplify_one_pass(*expr);
                match expr {
                    Expr::True => Expr::False,
                    Expr::False => Expr::True,
                    Expr::Not(inner) => *inner,
                    Expr::Lit { coord, values } => {
                        let complement = (0..self.universe.domain_sizes[coord])
                            .filter(|value| !values.contains(value))
                            .collect();
                        self.simplify_one_pass(Expr::Lit {
                            coord,
                            values: complement,
                        })
                    }
                    other => Expr::Not(Box::new(other)),
                }
            }
            Expr::And(args) => self.simplify_variadic(args, true),
            Expr::Or(args) => self.simplify_variadic(args, false),
        }
    }

    fn simplify_variadic(&self, args: Vec<Expr>, is_and: bool) -> Expr {
        let mut flat = Vec::new();
        for arg in args {
            let arg = self.simplify_one_pass(arg);
            match (&arg, is_and) {
                (Expr::False, true) => return Expr::False,
                (Expr::True, false) => return Expr::True,
                (Expr::True, true) | (Expr::False, false) => continue,
                (Expr::And(inner), true) => flat.extend(inner.iter().cloned()),
                (Expr::Or(inner), false) => flat.extend(inner.iter().cloned()),
                _ => flat.push(arg),
            }
        }

        let deduped = BTreeSet::<Expr>::from_iter(flat)
            .into_iter()
            .collect::<Vec<_>>();
        let merged = if is_and {
            self.merge_same_coordinate_literals_in_and(deduped)
        } else {
            self.merge_same_coordinate_literals_in_or(deduped)
        };
        self.finish_variadic(merged, is_and)
    }

    fn merge_same_coordinate_literals_in_and(&self, args: Vec<Expr>) -> Vec<Expr> {
        let mut groups = BTreeMap::<usize, BTreeSet<usize>>::new();
        let mut others = Vec::new();

        for arg in args {
            match arg {
                Expr::Lit { coord, values } => {
                    groups
                        .entry(coord)
                        .and_modify(|existing| {
                            *existing = existing.intersection(&values).copied().collect();
                        })
                        .or_insert(values);
                }
                other => others.push(other),
            }
        }

        for (coord, values) in groups {
            let lit = self.simplify_one_pass(Expr::Lit { coord, values });
            if lit == Expr::False {
                return vec![Expr::False];
            }
            if lit != Expr::True {
                others.push(lit);
            }
        }

        others.sort();
        others.dedup();
        others
    }

    fn merge_same_coordinate_literals_in_or(&self, args: Vec<Expr>) -> Vec<Expr> {
        let mut groups = BTreeMap::<usize, BTreeSet<usize>>::new();
        let mut others = Vec::new();

        for arg in args {
            match arg {
                Expr::Lit { coord, values } => {
                    groups
                        .entry(coord)
                        .and_modify(|existing| existing.extend(values.iter().copied()))
                        .or_insert(values);
                }
                other => others.push(other),
            }
        }

        for (coord, values) in groups {
            let lit = self.simplify_one_pass(Expr::Lit { coord, values });
            if lit == Expr::True {
                return vec![Expr::True];
            }
            if lit != Expr::False {
                others.push(lit);
            }
        }

        others.sort();
        others.dedup();
        others
    }

    fn finish_variadic(&self, mut args: Vec<Expr>, is_and: bool) -> Expr {
        match args.len() {
            0 => {
                if is_and {
                    Expr::True
                } else {
                    Expr::False
                }
            }
            1 => args.pop().unwrap(),
            _ => {
                if is_and {
                    Expr::And(args)
                } else {
                    Expr::Or(args)
                }
            }
        }
    }
}

fn remove_at(coords: &[usize], index: usize) -> Vec<usize> {
    coords
        .iter()
        .enumerate()
        .filter_map(|(i, &coord)| (i != index).then_some(coord))
        .collect()
}

fn word_len(bit_len: usize) -> usize {
    bit_len.div_ceil(64)
}

fn clear_unused_tail_bits(bits: &mut [u64], bit_len: usize) {
    let used = bit_len % 64;
    if used != 0
        && let Some(last) = bits.last_mut()
    {
        *last &= (1u64 << used) - 1;
    }
}

fn set_bit(bits: &mut [u64], index: usize) {
    bits[index / 64] |= 1u64 << (index % 64);
}

fn get_bit(bits: &[u64], index: usize) -> bool {
    (bits[index / 64] & (1u64 << (index % 64))) != 0
}

fn is_empty(bits: &[u64]) -> bool {
    bits.iter().all(|word| *word == 0)
}

fn complement_bits(bits: &[u64], bit_len: usize) -> Vec<u64> {
    let mut complement = bits.iter().map(|word| !word).collect::<Vec<_>>();
    clear_unused_tail_bits(&mut complement, bit_len);
    complement
}

fn values_from_bits(bits: &[u64], value_count: usize) -> BTreeSet<usize> {
    (0..value_count)
        .filter(|&index| get_bit(bits, index))
        .collect()
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{Expr, Solver, Universe};

    fn solve(universe: &Universe, tuples: &[&[usize]]) -> Expr {
        let coords = universe.all_coordinates();
        let mut bits = universe.empty_bits(&coords);
        for tuple in tuples {
            universe.set_tuple_bit(&coords, &mut bits, tuple);
        }
        Solver::new(universe).solve(bits)
    }

    fn assert_matches_target(universe: &Universe, expr: &Expr, expected: &[&[usize]]) {
        let expected = expected.iter().copied().collect::<BTreeSet<_>>();
        let coords = universe.all_coordinates();
        let domain_size = universe.domain_size(&coords);

        for index in 0..domain_size {
            let tuple = decode_full_tuple(universe, index);
            let actual = universe.evaluate(expr, &tuple);
            let wanted = expected.contains(&tuple.as_slice());
            assert_eq!(actual, wanted, "tuple {tuple:?}");
        }
    }

    fn decode_full_tuple(universe: &Universe, mut index: usize) -> Vec<usize> {
        let coords = universe.all_coordinates();
        let mut tuple = vec![0; coords.len()];
        for pos in (0..coords.len()).rev() {
            let radix = universe.domain_size(&coords[pos..=pos]);
            tuple[pos] = index % radix;
            index /= radix;
        }
        tuple
    }

    #[test]
    fn handles_empty_and_full_targets() {
        let universe = Universe::new(vec![2, 2]);

        let empty = solve(&universe, &[]);
        assert_eq!(empty, Expr::False);

        let full = solve(&universe, &[&[0, 0], &[0, 1], &[1, 0], &[1, 1]]);
        assert_eq!(full, Expr::True);
    }

    #[test]
    fn simplifies_single_coordinate_by_complement() {
        let universe = Universe::new(vec![3]);
        let expr = solve(&universe, &[&[0], &[2]]);

        assert_eq!(
            expr,
            Expr::Lit {
                coord: 0,
                values: [0, 2].into_iter().collect()
            }
        );
        assert_matches_target(&universe, &expr, &[&[0], &[2]]);
        assert_eq!(universe.expr_size(&expr), 2);
    }

    #[test]
    fn groups_equal_cofactors_into_single_literal() {
        let universe = Universe::new(vec![2, 2]);
        let expr = solve(&universe, &[&[0, 0], &[0, 1]]);

        assert_eq!(
            expr,
            Expr::Lit {
                coord: 0,
                values: [0].into_iter().collect()
            }
        );
        assert_matches_target(&universe, &expr, &[&[0, 0], &[0, 1]]);
    }

    #[test]
    fn keeps_disjunction_across_values_on_one_coordinate() {
        let universe = Universe::new(vec![3, 2]);
        let expr = solve(&universe, &[&[0, 0], &[0, 1], &[2, 0], &[2, 1]]);

        assert_eq!(
            expr,
            Expr::Lit {
                coord: 0,
                values: [0, 2].into_iter().collect()
            }
        );
        assert_matches_target(&universe, &expr, &[&[0, 0], &[0, 1], &[2, 0], &[2, 1]]);
    }

    #[test]
    fn uses_complement_when_it_is_smaller() {
        let universe = Universe::new(vec![2, 2]);
        let expr = solve(&universe, &[&[0, 0], &[0, 1], &[1, 0]]);

        assert_eq!(
            expr,
            Expr::Not(Box::new(Expr::And(vec![
                Expr::Lit {
                    coord: 0,
                    values: [1].into_iter().collect(),
                },
                Expr::Lit {
                    coord: 1,
                    values: [1].into_iter().collect(),
                },
            ])))
        );
        assert_matches_target(&universe, &expr, &[&[0, 0], &[0, 1], &[1, 0]]);
    }

    #[test]
    fn solver_instances_do_not_share_memo_across_universes() {
        let universe_a = Universe::new(vec![2, 2]);
        let expr_a = solve(&universe_a, &[&[0, 0], &[0, 1]]);
        assert_matches_target(&universe_a, &expr_a, &[&[0, 0], &[0, 1]]);

        let universe_b = Universe::new(vec![3, 2]);
        let expr_b = solve(&universe_b, &[&[0, 0], &[2, 1]]);
        assert_matches_target(&universe_b, &expr_b, &[&[0, 0], &[2, 1]]);
    }
}
