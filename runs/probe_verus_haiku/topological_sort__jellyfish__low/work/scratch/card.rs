use vstd::prelude::*;
verus! {
proof fn lemma_card(w: Seq<int>)
    requires
        forall |i: int, j: int| 0 <= i < j < w.len() ==> w[i] != w[j],
    ensures
        w.to_set().len() == w.len(),
    decreases w.len()
{
    if w.len() == 0 {
        assert(w.to_set() =~= Set::<int>::empty());
    } else {
        let t = w.drop_last();
        assert forall |i: int, j: int| 0 <= i < j < t.len() implies t[i] != t[j] by {
            assert(t[i] == w[i]);
            assert(t[j] == w[j]);
        }
        lemma_card(t);
        assert(w.drop_last() == t);
        assert forall |a: int| #[trigger] w.to_set().contains(a) <==> t.to_set().insert(w.last()).contains(a) by {
            if w.contains(a) {
                let k = choose |k: int| 0 <= k < w.len() && w[k] == a;
                if k == w.len() - 1 { assert(a == w.last()); } else { assert(t[k] == a); }
            }
            if t.contains(a) {
                let k = choose |k: int| 0 <= k < t.len() && t[k] == a;
                assert(w[k] == a);
            }
        }
        assert(w.to_set() =~= t.to_set().insert(w.last()));
        assert(!t.to_set().contains(w.last())) by {
            if t.contains(w.last()) {
                let k = choose |k: int| 0 <= k < t.len() && t[k] == w.last();
                assert(w[k] == w[w.len() - 1]);
            }
        }
        assert(t.to_set().insert(w.last()).len() == t.to_set().len() + 1);
    }
}

proof fn lemma_bound(w: Seq<int>, n: int)
    requires
        forall |i: int, j: int| 0 <= i < j < w.len() ==> w[i] != w[j],
        forall |i: int| 0 <= i < w.len() ==> 0 <= #[trigger] w[i] < n,
        0 <= n,
    ensures
        w.len() <= n,
{
    lemma_card(w);
    vstd::set_lib::lemma_int_range(0, n);
    assert forall |a: int| #[trigger] w.to_set().contains(a) implies vstd::set_lib::set_int_range(0, n).contains(a) by {
        let k = choose |k: int| 0 <= k < w.len() && w[k] == a;
    }
    assert(w.to_set().subset_of(vstd::set_lib::set_int_range(0, n)));
    vstd::set_lib::lemma_len_subset(w.to_set(), vstd::set_lib::set_int_range(0, n));
}
fn main() {}
}
