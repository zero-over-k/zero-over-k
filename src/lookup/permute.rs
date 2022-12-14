use std::collections::BTreeMap;

use ark_ff::Field;

pub fn permute_for_lookup<F: Field>(a: &[F], s: &[F]) -> (Vec<F>, Vec<F>) {
    assert_eq!(a.len(), s.len());

    let mut a_permuted = a[..].to_vec();
    a_permuted.sort();

    let mut table_element_counts = BTreeMap::<F, usize>::default();
    for &si in s {
        let count = table_element_counts.entry(si).or_insert(0);
        *count += 1
    }

    let mut permuted_table = vec![F::zero(); a.len()];

    let mut unassigned_indices = Vec::<usize>::new();

    for (index, &a_prime_i) in a_permuted.iter().enumerate() {
        if index == 0 || a_prime_i != a_permuted[index - 1] {
            permuted_table[index] = a_prime_i;
            if let Some(cnt) = table_element_counts.get_mut(&a_prime_i) {
                *cnt -= 1;
            } else {
                panic!("Element {} not found in table", a_prime_i)
            }
        } else {
            unassigned_indices.push(index);
        }
    }

    for (&el, &cnt) in table_element_counts.iter() {
        for _ in 0..cnt {
            let index_to_assign = unassigned_indices.pop().unwrap();
            permuted_table[index_to_assign] = el;
        }
    }

    assert!(unassigned_indices.is_empty());
    (a_permuted, permuted_table)
}

#[cfg(test)]
mod test {
    use super::permute_for_lookup;
    use ark_bls12_381::Fr as F;
    #[test]
    fn test_stitches() {
        let a = vec![
            5, 5, 1, 2, 1, 3, 1, 2, 3, 4, 1, 2, 3, 1, 6, 6, 6, 6, 6, 6, 11, 11,
            11, 11, 22, 22, 33, 33, 100,
        ];
        let s = [
            1, 2, 45, 9, 5, 21, 99, 2, 3, 4, 1, 2, 3, 11, 19, 2, 3, 1, 2, 13,
            22, 1, 3, 5, 100, 100, 22, 33, 6, 6, 611, 87, 37, 27, 28, 100, 33,
            22, 11,
        ];
        assert!(s.len() > a.len());

        let convert_to_field = |x: &[usize]| -> Vec<F> {
            x.iter().map(|&xi| F::from(xi as u64)).collect()
        };

        let mut a = convert_to_field(&a);
        let s = convert_to_field(&s);

        let dummy_s = F::from(99_u64);
        let to_append = s.len() - a.len();

        let append_vec = vec![dummy_s; to_append];

        a.extend_from_slice(&append_vec);
        assert_eq!(a.len(), s.len());

        let (a_permuted, s_permuted) = permute_for_lookup(&a, &s);
        assert_eq!(a_permuted[0], s_permuted[0]);

        for i in 1..a_permuted.len() {
            if a_permuted[i] != a_permuted[i - 1]
                && a_permuted[i] != s_permuted[i]
            {
                panic!("Something wrong")
            }
        }
    }
}
