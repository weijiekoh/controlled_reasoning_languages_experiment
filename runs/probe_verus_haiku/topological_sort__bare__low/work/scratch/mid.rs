    proof fn lemma_topo(graph: &Graph, done: Seq<bool>, order: Seq<usize>)
        requires
            graph.well_formed(),
            inv_order(graph.view(), done, order),
            forall |x: int| 0 <= x < graph.view().len() ==> done[x],
        ensures
            is_topological_ordering(graph.view(), order.map_values(|v: usize| v as int)),
    {
        let g = graph.view();
        let n = g.len() as int;
        let mi = order.map_values(|v: usize| v as int);
        assert(mi.no_duplicates()) by {
            assert forall |i: int, j: int| 0 <= i < mi.len() && 0 <= j < mi.len() && i != j implies mi[i] != mi[j] by {
                assert(order[i] != order[j]);
            }
        }
        assert forall |x: int| 0 <= x < n implies covered_by(order, x) by {
            assert(done[x]);
        }
        lemma_bound_u(order, n);
        lemma_full_u(order, n);
        assert(order.len() == n);
        assert(mi.len() == n);
        assert forall |x: int| 0 <= x < n implies mi.contains(x) by {
            assert(covered_by(order, x));
            let i = choose |i: int| 0 <= i < order.len() && order[i] as int == x;
            assert(mi[i] == x);
        }
        assert forall |i: int, j: int| 0 <= j < i < mi.len() implies !has_edge(g, #[trigger] mi[i], #[trigger] mi[j]) by {
            if has_edge(g, mi[i], mi[j]) {
                let kk = choose |kk: int| 0 <= kk < g[mi[i]].len() && #[trigger] g[mi[i]][kk] == mi[j];
                assert(g[order[i] as int][kk] == order[j] as int);
                assert(exists |jj: int| 0 <= jj < j && order[jj] as int == order[i] as int);
                let jj = choose |jj: int| 0 <= jj < j && order[jj] as int == order[i] as int;
                assert(order[jj] != order[i]);
            }
        }
    }

    proof fn lemma_step(graph: &Graph, od: Seq<bool>, oo: Seq<usize>, c: usize)
        requires
            graph.well_formed(),
            inv_order(graph.view(), od, oo),
            (c as int) < graph.view().len(),
            !od[c as int],
            ready_spec(graph.view(), od, c as int),
        ensures
            inv_order(graph.view(), od.update(c as int, true), oo.push(c)),
    {
        let g = graph.view();
        let nd = od.update(c as int, true);
        let no = oo.push(c);
        assert(nd.len() == od.len());
        assert forall |i: int| 0 <= i < no.len() implies (no[i] as int) < g.len() && nd[no[i] as int] by {
            if i < oo.len() {
                assert(no[i] == oo[i]);
                assert(oo[i] as int != c as int);
            } else {
                assert(no[i] == c);
            }
        }
        assert forall |x: int| 0 <= x < g.len() && nd[x] implies exists |i: int| 0 <= i < no.len() && no[i] as int == x by {
            if x == c as int {
                assert(no[oo.len() as int] == c);
            } else {
                assert(od[x]);
                let i0 = choose |i: int| 0 <= i < oo.len() && oo[i] as int == x;
                assert(no[i0] == oo[i0]);
            }
        }
        assert forall |i: int, j: int| 0 <= i < no.len() && 0 <= j < no.len() && i != j implies no[i] != no[j] by {
            if i < oo.len() && j < oo.len() {
                assert(oo[i] != oo[j]);
            } else if i < oo.len() {
                assert(oo[i] as int != c as int);
            } else {
                assert(oo[j] as int != c as int);
            }
        }
        assert forall |i: int, u: int, k: int|
                0 <= i < no.len() && 0 <= u < g.len() && 0 <= k < g[u].len() && g[u][k] == no[i] as int
                implies exists |j: int| 0 <= j < i && no[j] as int == u by {
            if i < oo.len() {
                assert(no[i] == oo[i]);
            } else {
                assert(no[i] == c);
                assert(od[u]);
                let j0 = choose |j: int| 0 <= j < oo.len() && oo[j] as int == u;
                assert(no[j0] == oo[j0]);
            }
        }
    }

