use std::collections::BTreeMap;

fn permute_for_lookup(a: &[usize], s: &[usize]) -> (Vec<usize>, Vec<usize>) {
    assert_eq!(a.len(), s.len());

    let mut a_permuted = a[..].to_vec();
    a_permuted.sort();

    let mut stitches_to_indices =
        BTreeMap::<usize, usize>::from([(a_permuted[0], 0)]);
    for i in 1..a_permuted.len() {
        if a_permuted[i] != a_permuted[i - 1] {
            stitches_to_indices.insert(a_permuted[i], i);
        }
    }

    // at start s_permuted is same as s
    let mut s_permuted = s[..].to_vec();

    for s_index in 0..s_permuted.len() {
        if stitches_to_indices.is_empty() {
            break;
        }
        let si = s_permuted[s_index];
        match stitches_to_indices.get(&si) {
            Some(stitch_index) => {
                // this means that si is some stitch

                // if stitch_index = s_index then it's already on proper place
                // else:
                if stitch_index.clone() != s_index {
                    s_permuted[s_index] = s_permuted[stitch_index.clone()]; // put here whatever was at stitch_index
                    s_permuted[stitch_index.clone()] = si; // stitch was at s_index, move it to stitch_index place
                }

                stitches_to_indices.remove(&si);
            }
            None => (),
        }
    }
    assert_eq!(true, stitches_to_indices.is_empty());
    (a_permuted, s_permuted)
}

#[cfg(test)]
mod test {
    use super::permute_for_lookup;
    #[test]
    fn test_stitches() {
        let mut a = vec![
            5, 5, 1, 2, 1, 3, 1, 2, 3, 4, 1, 2, 3, 1, 6, 6, 6, 6, 6, 6, 11, 11,
            11, 11, 22, 22, 33, 33, 100,
        ];
        let s = [
            1, 2, 45, 9, 5, 21, 99, 2, 3, 4, 1, 2, 3, 11, 19, 2, 3, 1, 2, 13,
            22, 1, 3, 5, 100, 100, 22, 33, 6, 6, 611, 87, 37, 27, 28, 100, 33,
            22, 11,
        ];
        assert!(s.len() > a.len());

        let dummy_s = 99;
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
