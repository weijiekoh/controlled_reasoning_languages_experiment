    pub open spec fn inv_order(g: Seq<Seq<int>>, done: Seq<bool>, order: Seq<usize>) -> bool {
        &&& done.len() == g.len()
        &&& forall |i: int| 0 <= i < order.len() ==> (order[i] as int) < g.len() && done[order[i] as int]
        &&& forall |x: int| 0 <= x < g.len() && done[x] ==> exists |i: int| 0 <= i < order.len() && order[i] as int == x
        &&& forall |i: int, j: int| 0 <= i < order.len() && 0 <= j < order.len() && i != j ==> order[i] != order[j]
        &&& forall |i: int, u: int, k: int| #![trigger g[u][k], order[i]]
                0 <= i < order.len() && 0 <= u < g.len() && 0 <= k < g[u].len() && g[u][k] == order[i] as int
                ==> exists |j: int| 0 <= j < i && order[j] as int == u
    }

    pub open spec fn ready_spec(g: Seq<Seq<int>>, done: Seq<bool>, v: int) -> bool {
        forall |u: int, k: int| 0 <= u < g.len() && 0 <= k < g[u].len() && g[u][k] == v ==> done[u]
    }

    proof fn lemma_view_idx(graph: &Graph)
        ensures
            graph.view().len() == graph.adj.len(),
            forall |u: int, k: int| 0 <= u < graph.adj.len() && 0 <= k < graph.adj[u].len()
                ==> graph.view()[u][k] == graph.adj[u][k] as int,
    {
        assert forall |u: int, k: int| 0 <= u < graph.adj.len() && 0 <= k < graph.adj[u].len()
            implies graph.view()[u][k] == graph.adj[u][k] as int by {
            assert(graph.view()[u] == Seq::new(graph.adj[u].len() as nat, |j: int| graph.adj[u][j] as int));
        }
    }

    proof fn lemma_edge_in_range(graph: &Graph, u: int, v: int)
        requires
            graph.well_formed(),
            has_edge(graph.view(), u, v),
        ensures
            0 <= u < graph.view().len(),
            0 <= v < graph.view().len(),
    {
        let i = choose |i: int| 0 <= u < graph.view().len() && 0 <= i < graph.view()[u].len() && graph.view()[u][i] == v;
        assert(0 <= v < graph.view().len()) by {
            assert(0 <= graph.view()[u][i] < graph.view().len());
        }
    }

    proof fn lemma_bound_int(s: Seq<int>, n: int)
        requires
            0 <= n,
            s.no_duplicates(),
            forall |i: int| 0 <= i < s.len() ==> 0 <= #[trigger] s[i] < n,
        ensures
            s.len() <= n,
    {
        s.unique_seq_to_set();
        vstd::set_lib::lemma_int_range(0, n);
        let r = vstd::set_lib::set_int_range(0, n);
        assert(s.to_set().subset_of(r)) by {
            assert forall |x: int| s.to_set().contains(x) implies r.contains(x) by {
                assert(s.contains(x));
            }
        }
        vstd::set_lib::lemma_len_subset(s.to_set(), r);
    }

    proof fn lemma_bound_u(s: Seq<usize>, n: int)
        requires
            0 <= n,
            s.no_duplicates(),
            forall |i: int| 0 <= i < s.len() ==> (s[i] as int) < n,
        ensures
            s.len() <= n,
    {
        let mi = s.map_values(|v: usize| v as int);
        assert(mi.no_duplicates());
        lemma_bound_int(mi, n);
    }

    // a distinct sequence of values in [0, n) that misses x has length < n
    proof fn lemma_cover(s: Seq<usize>, n: int, x: int)
        requires
            0 <= n,
            s.no_duplicates(),
            forall |i: int| 0 <= i < s.len() ==> (s[i] as int) < n,
            0 <= x < n,
            forall |i: int| 0 <= i < s.len() ==> s[i] as int != x,
        ensures
            s.len() <= n - 1,
    {
        let t = s.map_values(|v: usize| if (v as int) < x { v as int } else { v as int - 1 });
        assert(t.no_duplicates()) by {
            assert forall |i: int, j: int| 0 <= i < t.len() && 0 <= j < t.len() && i != j implies t[i] != t[j] by {
                assert(s[i] != s[j]);
            }
        }
        assert forall |i: int| 0 <= i < t.len() implies 0 <= #[trigger] t[i] < n - 1 by {
            assert(s[i] as int != x);
        }
        lemma_bound_int(t, n - 1);
    }

    pub open spec fn covered_by(s: Seq<usize>, x: int) -> bool {
        exists |i: int| 0 <= i < s.len() && s[i] as int == x
    }

    proof fn lemma_full_u(s: Seq<usize>, n: int)
        requires
            0 <= n,
            s.no_duplicates(),
            forall |i: int| 0 <= i < s.len() ==> (s[i] as int) < n,
            forall |x: int| 0 <= x < n ==> #[trigger] covered_by(s, x),
        ensures
            s.len() >= n,
    {
        let mi = s.map_values(|v: usize| v as int);
        assert(mi.no_duplicates());
        assert(forall |i: int| 0 <= i < mi.len() ==> 0 <= #[trigger] mi[i] < n);
        assert(mi.to_set().len() == mi.len()) by {
            mi.unique_seq_to_set();
        }
        vstd::set_lib::lemma_int_range(0, n);
        let r = vstd::set_lib::set_int_range(0, n);
        assert(r.subset_of(mi.to_set())) by {
            assert forall |x: int| r.contains(x) implies mi.to_set().contains(x) by {
                assert(covered_by(s, x));
                let i = choose |i: int| 0 <= i < s.len() && s[i] as int == x;
                assert(mi[i] == x);
                assert(mi.contains(x));
            }
        }
        vstd::set_lib::lemma_len_subset(r, mi.to_set());
    }

    proof fn lemma_path_range(graph: &Graph, p: Seq<int>)
        requires
            graph.well_formed(),
            is_path(graph.view(), p),
            p.len() > 1,
        ensures
            forall |x: int| 0 <= x < p.len() ==> 0 <= #[trigger] p[x] < graph.view().len(),
    {
        assert forall |x: int| 0 <= x < p.len() implies 0 <= #[trigger] p[x] < graph.view().len() by {
            if x < p.len() - 1 {
                assert(has_edge(graph.view(), p[x], p[x + 1]));
                lemma_edge_in_range(graph, p[x], p[x + 1]);
            } else {
                assert(has_edge(graph.view(), p[x - 1], p[x]));
                lemma_edge_in_range(graph, p[x - 1], p[x]);
            }
        }
    }

    proof fn lemma_chain(graph: &Graph, done: Seq<bool>, order: Seq<usize>, p: Seq<int>, a: int, k: int)
        requires
            graph.well_formed(),
            inv_order(graph.view(), done, order),
            forall |x: int| 0 <= x < graph.view().len() ==> done[x],
            is_path(graph.view(), p),
            forall |x: int| 0 <= x < p.len() ==> 0 <= #[trigger] p[x] < graph.view().len(),
            0 <= a < order.len(),
            order[a] as int == p[0],
            0 <= k < p.len(),
        ensures
            exists |b: int| 0 <= b < order.len() && order[b] as int == p[k] && b >= a + k,
        decreases k,
    {
        if k == 0 {
            assert(order[a] as int == p[0]);
        } else {
            lemma_chain(graph, done, order, p, a, k - 1);
            let b1 = choose |b: int| 0 <= b < order.len() && order[b] as int == p[k - 1] && b >= a + k - 1;
            assert(done[p[k]]);
            let c = choose |i: int| 0 <= i < order.len() && order[i] as int == p[k];
            assert(has_edge(graph.view(), p[k - 1], p[k]));
            let kk = choose |i: int| 0 <= i < graph.view()[p[k - 1]].len() && #[trigger] graph.view()[p[k - 1]][i] == p[k];
            assert(0 <= p[k - 1] < graph.view().len() && 0 <= kk < graph.view()[p[k - 1]].len() && graph.view()[p[k - 1]][kk] == order[c] as int);
            let j = choose |j: int| 0 <= j < c && order[j] as int == p[k - 1];
            assert(j == b1) by {
                if j < b1 {
                    assert(order[j] != order[b1]);
                } else if b1 < j {
                    assert(order[b1] != order[j]);
                }
            }
            assert(0 <= c < order.len() && order[c] as int == p[k] && c >= a + k);
        }
    }

    proof fn lemma_acyclic(graph: &Graph, done: Seq<bool>, order: Seq<usize>, p: Seq<int>)
        requires
            graph.well_formed(),
            inv_order(graph.view(), done, order),
            forall |x: int| 0 <= x < graph.view().len() ==> done[x],
            is_cycle(graph.view(), p),
        ensures
            false,
    {
        lemma_path_range(graph, p);
        assert(done[p[0]]);
        let a = choose |i: int| 0 <= i < order.len() && order[i] as int == p[0];
        lemma_chain(graph, done, order, p, a, p.len() - 1);
        let b = choose |b: int| 0 <= b < order.len() && order[b] as int == p[p.len() - 1] && b >= a + p.len() - 1;
        assert(order[b] == order[a]);
        assert(b == a);
    }

    proof fn lemma_no_cycle(graph: &Graph, done: Seq<bool>, order: Seq<usize>)
        requires
            graph.well_formed(),
            inv_order(graph.view(), done, order),
            forall |x: int| 0 <= x < graph.view().len() ==> done[x],
        ensures
            !graph_has_cycle(graph.view()),
    {
        if graph_has_cycle(graph.view()) {
            let p = choose |p: Seq<int>| is_cycle(graph.view(), p);
            lemma_acyclic(graph, done, order, p);
        }
    }

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
        assert forall |i: int, u: int, k: int| #![trigger g[u][k], no[i]]
                0 <= i < no.len() && 0 <= u < g.len() && 0 <= k < g[u].len() && g[u][k] == no[i] as int
                implies exists |j: int| 0 <= j < i && no[j] as int == u by {
            if i < oo.len() {
                assert(no[i] == oo[i]);
                assert(g[u][k] == oo[i] as int);
                assert(exists |j: int| 0 <= j < i && oo[j] as int == u);
                let j1 = choose |j: int| 0 <= j < i && oo[j] as int == u;
                assert(no[j1] == oo[j1]);
            } else {
                assert(no[i] == c);
                assert(g[u][k] == c as int);
                assert(0 <= u < g.len() && 0 <= k < g[u].len() && g[u][k] == c as int ==> od[u]) by {
                    assert(ready_spec(g, od, c as int));
                }
                assert(od[u]);
                let j0 = choose |j: int| 0 <= j < oo.len() && oo[j] as int == u;
                assert(no[j0] == oo[j0]);
                assert(0 <= j0 < i && no[j0] as int == u);
            }
        }
    }

    proof fn lemma_cycle_build(graph: &Graph, walk: Seq<usize>, a: int)
        requires
            walk.len() >= 1,
            forall |k: int| 0 <= k < walk.len() - 1 ==> has_edge(graph.view(), walk[k + 1] as int, #[trigger] walk[k] as int),
            0 <= a < walk.len(),
            has_edge(graph.view(), walk[a] as int, walk[walk.len() - 1] as int),
        ensures
            graph_has_cycle(graph.view()),
    {
        let last = walk.len() - 1;
        let pc = Seq::new((last - a + 2) as nat, |i: int| if i == 0 { walk[a] as int } else { walk[last + 1 - i] as int });
        assert(pc.len() == last - a + 2);
        assert forall |i: int| 0 <= i < pc.len() - 1 implies has_edge(graph.view(), #[trigger] pc[i], pc[i + 1]) by {
            if i == 0 {
                assert(pc[0] == walk[a] as int);
                assert(pc[1] == walk[last] as int);
            } else {
                assert(pc[i] == walk[last + 1 - i] as int);
                assert(pc[i + 1] == walk[last - i] as int);
                assert(has_edge(graph.view(), walk[last - i + 1] as int, walk[last - i] as int));
            }
        }
        assert(is_path(graph.view(), pc));
        assert(pc.len() > 1);
        assert(pc.last() == pc[pc.len() - 1]);
        assert(pc[0] == pc[pc.len() - 1]);
        assert(is_cycle(graph.view(), pc));
    }

    fn find_pred(graph: &Graph, done: &Vec<bool>, v: usize) -> (res: Option<(usize, usize)>)
        requires
            graph.well_formed(),
            done@.len() == graph.adj.len(),
            v < graph.adj.len(),
        ensures
            match res {
                Some((u, k)) => u < graph.adj.len() && k < graph.adj[u as int].len()
                    && graph.adj[u as int][k as int] == v && !done@[u as int],
                None => ready_spec(graph.view(), done@, v as int),
            }
    {
        proof { lemma_view_idx(graph); }
        let n = graph.adj.len();
        let mut u: usize = 0;
        while u < n
            invariant
                n == graph.adj.len(),
                done@.len() == n,
                v < n,
                u <= n,
                forall |x: int, k: int| 0 <= x < u && 0 <= k < graph.view()[x].len() && graph.view()[x][k] == v as int
                    ==> done@[x],
            decreases n - u,
        {
            let mut k: usize = 0;
            while k < graph.adj[u].len()
                invariant
                    n == graph.adj.len(),
                    done@.len() == n,
                    v < n,
                    u < n,
                    k <= graph.adj[u as int].len(),
                    forall |x: int, kk: int| 0 <= x < u && 0 <= kk < graph.view()[x].len() && graph.view()[x][kk] == v as int
                        ==> done@[x],
                    forall |kk: int| 0 <= kk < k && graph.view()[u as int][kk] == v as int ==> done@[u as int],
                decreases graph.adj[u as int].len() - k,
            {
                if graph.adj[u][k] == v && !done[u] {
                    return Some((u, k));
                }
                k += 1;
            }
            u += 1;
        }
        None
    }

    fn find_index(walk: &Vec<usize>, x: usize) -> (r: Option<usize>)
        ensures
            match r {
                Some(a) => a < walk.len() && walk@[a as int] == x,
                None => forall |i: int| 0 <= i < walk.len() ==> walk@[i] != x,
            }
    {
        let mut i: usize = 0;
        while i < walk.len()
            invariant
                i <= walk.len(),
                forall |j: int| 0 <= j < i ==> walk@[j] != x,
            decreases walk.len() - i,
        {
            if walk[i] == x {
                return Some(i);
            }
            i += 1;
        }
        None
    }
