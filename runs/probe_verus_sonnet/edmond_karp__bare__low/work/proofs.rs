    proof fn ssum_ext(n: int, h1: spec_fn(int) -> int, h2: spec_fn(int) -> int)
        requires forall |k: int| 0 <= k < n ==> #[trigger] h1(k) == h2(k)
        ensures ssum(n, h1) == ssum(n, h2)
        decreases n
    {
        if n > 0 { ssum_ext(n - 1, h1, h2); }
    }

    proof fn ssum_add(n: int, h1: spec_fn(int) -> int, h2: spec_fn(int) -> int, h3: spec_fn(int) -> int)
        requires forall |k: int| 0 <= k < n ==> #[trigger] h3(k) == h1(k) + h2(k)
        ensures ssum(n, h3) == ssum(n, h1) + ssum(n, h2)
        decreases n
    {
        if n > 0 { ssum_add(n - 1, h1, h2, h3); }
    }

    proof fn ssum_sub(n: int, h1: spec_fn(int) -> int, h2: spec_fn(int) -> int, h3: spec_fn(int) -> int)
        requires forall |k: int| 0 <= k < n ==> #[trigger] h3(k) == h1(k) - h2(k)
        ensures ssum(n, h3) == ssum(n, h1) - ssum(n, h2)
        decreases n
    {
        if n > 0 { ssum_sub(n - 1, h1, h2, h3); }
    }

    proof fn ssum_mono(n: int, h1: spec_fn(int) -> int, h2: spec_fn(int) -> int)
        requires forall |k: int| 0 <= k < n ==> #[trigger] h1(k) <= h2(k)
        ensures ssum(n, h1) <= ssum(n, h2)
        decreases n
    {
        if n > 0 { ssum_mono(n - 1, h1, h2); }
    }

    proof fn ssum_const(n: int, h: spec_fn(int) -> int, c: int)
        requires n >= 0, forall |k: int| 0 <= k < n ==> #[trigger] h(k) <= c
        ensures ssum(n, h) <= n * c
        decreases n
    {
        if n > 0 { ssum_const(n - 1, h, c); assert(h(n - 1) <= c); assert(n * c == (n - 1) * c + c) by (nonlinear_arith); } else { assert(n == 0); }
    }

    proof fn ssum_nonneg(n: int, h: spec_fn(int) -> int)
        requires forall |k: int| 0 <= k < n ==> #[trigger] h(k) >= 0
        ensures ssum(n, h) >= 0
        decreases n
    {
        if n > 0 { ssum_nonneg(n - 1, h); }
    }

    proof fn ssum_point(n: int, h: spec_fn(int) -> int, w: int, c: int)
        requires forall |k: int| 0 <= k < n ==> #[trigger] h(k) == (if k == w { c } else { 0 })
        ensures ssum(n, h) == (if 0 <= w < n { c } else { 0 })
        decreases n
    {
        if n > 0 { ssum_point(n - 1, h, w, c); }
    }

    proof fn ssum_swap(a: int, b: int, ff: spec_fn(int, int) -> int)
        requires a >= 0, b >= 0
        ensures ssum(a, |u: int| ssum(b, |v: int| ff(u, v))) == ssum(b, |v: int| ssum(a, |u: int| ff(u, v)))
        decreases a
    {
        if a > 0 {
            ssum_swap(a - 1, b, ff);
            let l1 = |u: int| ssum(b, |v: int| ff(u, v));
            ssum_ext(b, |v: int| ff(a - 1, v), |v: int| ff(a - 1, v));
            let r0 = |v: int| ssum(a - 1, |u: int| ff(u, v));
            let r1 = |v: int| ssum(a, |u: int| ff(u, v));
            let ra = |v: int| ff(a - 1, v);
            assert forall |v: int| 0 <= v < b implies #[trigger] r1(v) == r0(v) + ra(v) by {}
            ssum_add(b, r0, ra, r1);
            assert(ssum(a, l1) == ssum(a - 1, l1) + l1(a - 1));
            assert(l1(a - 1) == ssum(b, ra));
            assert(ssum(b, r1) == ssum(b, r0) + ssum(b, ra));
        } else {
            let z = |v: int| ssum(a, |u: int| ff(u, v));
            assert forall |v: int| 0 <= v < b implies #[trigger] z(v) == 0 by {}
            lemma_ssum_zero(b, z);
        }
    }

    // ---- capacity lemmas
    proof fn eidx_ok(g: Seq<Seq<(int, int)>>, u: int, v: int)
        requires has_edge(g, u, v)
        ensures 0 <= u < g.len(), 0 <= eidx(g, u, v) < g[u].len(), g[u][eidx(g, u, v)].0 == v
    {
        let i = choose |i: int| 0 <= u < g.len() && 0 <= i < g[u].len() && #[trigger] g[u][i].0 == v;
        assert(0 <= u < g.len() && 0 <= i < g[u].len() && g[u][i].0 == v);
    }

    proof fn capf_has(g: Seq<Seq<(int, int)>>, u: int, v: int)
        requires has_edge(g, u, v)
        ensures has_capacity(g, u, v, capf(g, u, v))
    {
        eidx_ok(g, u, v);
        let i = eidx(g, u, v);
        assert(g[u][i].0 == v && g[u][i].1 == capf(g, u, v));
    }

    proof fn capf_unique(g: Seq<Seq<(int, int)>>, u: int, v: int, c: int)
        requires wf(g), 0 <= u < g.len(), has_capacity(g, u, v, c)
        ensures has_edge(g, u, v), capf(g, u, v) == c
    {
        let i = choose |i: int| 0 <= u < g.len() && 0 <= i < g[u].len() && #[trigger] g[u][i].0 == v && g[u][i].1 == c;
        assert(g[u][i].0 == v);
        assert(has_edge(g, u, v));
        eidx_ok(g, u, v);
        let i2 = eidx(g, u, v);
        if i2 != i { assert(g[u][i2].0 != g[u][i].0); }
    }

    proof fn capf_bounds(g: Seq<Seq<(int, int)>>, u: int, v: int)
        requires wf(g), capacities_bounded(g), 0 <= u < g.len()
        ensures 0 <= capf(g, u, v) <= 100_000
    {
        if has_edge(g, u, v) {
            capf_has(g, u, v);
        }
    }

    proof fn valid_feas(g: Seq<Seq<(int, int)>>, f: FlowMap, s: int, t: int)
        requires wf(g), capacities_bounded(g), is_valid_flow(g, f, s, t)
        ensures feas(g, f)
    {
        assert forall |u: int, v: int| 0 <= u < g.len() && 0 <= v < g.len()
            implies 0 <= #[trigger] get_flow(f, u, v) && get_flow(f, u, v) <= capf(g, u, v) by {
            capf_bounds(g, u, v);
            if f.dom().contains((u, v)) {
                assert(f[(u, v)] >= 0);
                if f[(u, v)] > 0 {
                    let c = choose |c: int| has_capacity(g, u, v, c) && f[(u, v)] <= c;
                    capf_unique(g, u, v, c);
                }
            }
        }
    }

    proof fn feas_respects(g: Seq<Seq<(int, int)>>, f: FlowMap)
        requires wf(g), capacities_bounded(g), feas(g, f),
            forall |u: int, v: int| f.dom().contains((u, v)) ==> 0 <= u < g.len() && 0 <= v < g.len()
        ensures respects_capacity(g, f)
    {
        assert forall |u: int, v: int| #[trigger] f.dom().contains((u, v)) implies (                f[(u, v)] > 0 ==> (exists |c: int| has_capacity(g, u, v, c) && f[(u, v)] <= c)) by {
            if f[(u, v)] > 0 {
                assert(get_flow(f, u, v) == f[(u, v)]);
                assert(capf(g, u, v) > 0);
                assert(has_edge(g, u, v));
                capf_has(g, u, v);
            }
        }
    }

    // ---- in/out sums
    proof fn in_eq(g: Seq<Seq<(int, int)>>, f: FlowMap, u: int, k: int)
        requires k >= 0
        ensures sum_flow_in_recursive(g, f, u, k) == ssum(k, |v: int| get_flow(f, v, u))
        decreases k
    {
        if k > 0 { in_eq(g, f, u, k - 1); }
    }

    proof fn out_eq_step(g: Seq<Seq<(int, int)>>, f: FlowMap, u: int, k: int)
        requires wf(g), feas(g, f), 0 <= u < g.len(), 0 <= k <= g[u].len()
        ensures sum_flow_out_recursive(g, f, u, k) == ssum(g.len() as int, |v: int|
            if (exists |i: int| 0 <= i < k && #[trigger] g[u][i].0 == v) { get_flow(f, u, v) } else { 0 })
        decreases k
    {
        let n = g.len() as int;
        let hk = |v: int| if (exists |i: int| 0 <= i < k && #[trigger] g[u][i].0 == v) { get_flow(f, u, v) } else { 0 };
        if k == 0 {
            let z = |v: int| 0int;
            assert forall |v: int| 0 <= v < n implies #[trigger] hk(v) == z(v) by {}
            ssum_ext(n, hk, z);
            assert(ssum(n, z) == 0) by { lemma_ssum_zero(n, z); }
        } else {
            out_eq_step(g, f, u, k - 1);
            let hk1 = |v: int| if (exists |i: int| 0 <= i < k - 1 && #[trigger] g[u][i].0 == v) { get_flow(f, u, v) } else { 0 };
            let w = g[u][k - 1].0;
            assert(0 <= w < n);
            let e = |v: int| if v == w { get_flow(f, u, v) } else { 0 };
            assert forall |v: int| 0 <= v < n implies #[trigger] hk(v) == hk1(v) + e(v) by {
                if v == w {
                    assert(!(exists |i: int| 0 <= i < k - 1 && #[trigger] g[u][i].0 == v)) by {
                        if exists |i: int| 0 <= i < k - 1 && #[trigger] g[u][i].0 == v {
                            let i = choose |i: int| 0 <= i < k - 1 && #[trigger] g[u][i].0 == v;
                            assert(g[u][i].0 != g[u][k - 1].0);
                        }
                    }
                } else {
                    if exists |i: int| 0 <= i < k && #[trigger] g[u][i].0 == v {
                        let i = choose |i: int| 0 <= i < k && #[trigger] g[u][i].0 == v;
                        assert(i < k - 1);
                    }
                }
            }
            ssum_add(n, hk1, e, hk);
            assert forall |v: int| 0 <= v < n implies #[trigger] e(v) == (if v == w { get_flow(f, u, w) } else { 0 }) by {}
            ssum_point(n, e, w, get_flow(f, u, w));
        }
    }

    proof fn lemma_ssum_zero(n: int, z: spec_fn(int) -> int)
        requires forall |k: int| 0 <= k < n ==> #[trigger] z(k) == 0
        ensures ssum(n, z) == 0
        decreases n
    {
        if n > 0 { lemma_ssum_zero(n - 1, z); }
    }

    proof fn out_eq(g: Seq<Seq<(int, int)>>, f: FlowMap, u: int)
        requires wf(g), feas(g, f), 0 <= u < g.len()
        ensures total_flow_out(g, f, u) == outn(g.len() as int, f, u)
    {
        let n = g.len() as int;
        let len = g[u].len() as int;
        out_eq_step(g, f, u, len);
        let hk = |v: int| if (exists |i: int| 0 <= i < len && #[trigger] g[u][i].0 == v) { get_flow(f, u, v) } else { 0 };
        let o = |v: int| get_flow(f, u, v);
        assert forall |v: int| 0 <= v < n implies #[trigger] hk(v) == o(v) by {
            if !(exists |i: int| 0 <= i < len && #[trigger] g[u][i].0 == v) {
                assert(!has_edge(g, u, v));
                assert(capf(g, u, v) == 0);
            }
        }
        ssum_ext(n, hk, o);
    }

    // ---- cut lemma
    proof fn cut_eq(n: int, f: FlowMap, sset: spec_fn(int) -> bool, s: int, t: int)
        requires 0 <= s < n, 0 <= t < n, sset(s), !sset(t),
            forall |u: int| 0 <= u < n && u != s && u != t ==> net(n, f, u) == 0
        ensures -net(n, f, s) == cutval(n, f, sset)
    {
        let pp = |u: int, v: int| if sset(u) && sset(v) { dd(f, u, v) } else { 0int };
        let bb = |u: int, v: int| if sset(u) && !sset(v) { dd(f, u, v) } else { 0int };
        let aa = |u: int, v: int| if sset(u) { dd(f, u, v) } else { 0int };
        let nn = |u: int| if sset(u) { -net(n, f, u) } else { 0int };
        let ia = |u: int| ssum(n, |v: int| aa(u, v));
        let ip = |u: int| ssum(n, |v: int| pp(u, v));
        let ib = |u: int| ssum(n, |v: int| if sset(u) && !sset(v) { dd(f, u, v) } else { 0int });
        // (1)
        assert forall |u: int| 0 <= u < n implies -net(n, f, u) == ssum(n, |v: int| dd(f, u, v)) by {
            ssum_sub(n, |v: int| get_flow(f, u, v), |v: int| get_flow(f, v, u), |v: int| dd(f, u, v));
        }
        // (2)
        assert forall |u: int| 0 <= u < n implies #[trigger] nn(u) == (if u == s { -net(n, f, s) } else { 0 }) by {}
        ssum_point(n, nn, s, -net(n, f, s));
        // (3)
        assert forall |u: int| 0 <= u < n implies #[trigger] nn(u) == ia(u) by {
            if sset(u) {
                ssum_ext(n, |v: int| dd(f, u, v), |v: int| aa(u, v));
            } else {
                lemma_ssum_zero(n, |v: int| aa(u, v));
            }
        }
        ssum_ext(n, nn, ia);
        assert forall |u: int| 0 <= u < n implies #[trigger] ia(u) == ip(u) + ib(u) by {
            ssum_add(n, |v: int| pp(u, v), |v: int| bb(u, v), |v: int| aa(u, v));
            ssum_ext(n, |v: int| bb(u, v), |v: int| if sset(u) && !sset(v) { dd(f, u, v) } else { 0int });
        }
        ssum_add(n, ip, ib, ia);
        // X = 0
        let x = ssum(n, ip);
        ssum_swap(n, n, pp);
        let sw = |v: int| ssum(n, |u: int| pp(u, v));
        assert forall |v: int| 0 <= v < n implies #[trigger] sw(v) == -ip(v) by {
            ssum_sub(n, |u: int| 0int, |w: int| pp(v, w), |u: int| pp(u, v));
            lemma_ssum_zero(n, |u: int| 0int);
        }
        let negip = |v: int| -ip(v);
        ssum_ext(n, sw, negip);
        ssum_sub(n, |v: int| 0int, ip, negip);
        lemma_ssum_zero(n, |v: int| 0int);
        assert(ssum(n, |u: int| ssum(n, |v: int| pp(u, v))) == ssum(n, ip));
        assert(cutval(n, f, sset) == ssum(n, ib));
    }

    proof fn cut_mono(n: int, f: FlowMap, h: FlowMap, sset: spec_fn(int) -> bool)
        requires forall |u: int, v: int| 0 <= u < n && 0 <= v < n && sset(u) && !sset(v) ==> dd(h, u, v) <= dd(f, u, v)
        ensures cutval(n, h, sset) <= cutval(n, f, sset)
    {
        let bf = |u: int, v: int| if sset(u) && !sset(v) { dd(f, u, v) } else { 0int };
        let bh = |u: int, v: int| if sset(u) && !sset(v) { dd(h, u, v) } else { 0int };
        let ih = |u: int| ssum(n, |v: int| if sset(u) && !sset(v) { dd(h, u, v) } else { 0int });
        let iff = |u: int| ssum(n, |v: int| if sset(u) && !sset(v) { dd(f, u, v) } else { 0int });
        assert forall |u: int| 0 <= u < n implies #[trigger] ih(u) <= iff(u) by {
            ssum_mono(n, |v: int| if sset(u) && !sset(v) { dd(h, u, v) } else { 0int }, |v: int| if sset(u) && !sset(v) { dd(f, u, v) } else { 0int });
        }
        ssum_mono(n, ih, iff);
    }

    proof fn val_bound(g: Seq<Seq<(int, int)>>, f: FlowMap, s: int)
        requires wf(g), capacities_bounded(g), feas(g, f), 0 <= s < g.len()
        ensures -net(g.len() as int, f, s) <= g.len() * 100_000, -net(g.len() as int, f, s) >= -(g.len() * 100_000)
    {
        let n = g.len() as int;
        assert forall |v: int| 0 <= v < n implies get_flow(f, s, v) <= 100_000 by { capf_bounds(g, s, v); }
        ssum_const(n, |v: int| get_flow(f, s, v), 100_000);
        ssum_nonneg(n, |v: int| get_flow(f, v, s));
        ssum_nonneg(n, |v: int| get_flow(f, s, v));
        assert forall |v: int| 0 <= v < n implies get_flow(f, v, s) <= 100_000 by { capf_bounds(g, v, s); }
        ssum_const(n, |v: int| get_flow(f, v, s), 100_000);
    }

    proof fn fm_get(fl: Seq<Seq<i64>>, n: int, u: int, v: int)
        ensures get_flow(fm(fl, n), u, v) == (if 0 <= u < n && 0 <= v < n { fl[u][v] as int } else { 0int })
    {
        let f = fm(fl, n);
        if 0 <= u < n && 0 <= v < n {
            assert(f.dom().contains((u, v)));
        } else {
            assert(!f.dom().contains((u, v)));
        }
    }

    proof fn upd_net(fl: Seq<Seq<i64>>, fl2: Seq<Seq<i64>>, n: int, a: int, b: int, x: i64)
        requires shaped(fl, n), 0 <= a < n, 0 <= b < n,
            fl2 == fl.update(a, fl[a].update(b, x))
        ensures forall |u: int| 0 <= u < n ==>
            #[trigger] net(n, fm(fl2, n), u) == net(n, fm(fl, n), u)
                + (if u == b { x - fl[a][b] } else { 0int }) - (if u == a { x - fl[a][b] } else { 0int })
    {
        let d = x as int - fl[a][b] as int;
        let f = fm(fl, n);
        let f2 = fm(fl2, n);
        assert forall |u: int| 0 <= u < n implies
            #[trigger] net(n, f2, u) == net(n, f, u)
                + (if u == b { d } else { 0int }) - (if u == a { d } else { 0int }) by {
            assert forall |w: int, z: int| 0 <= w < n && 0 <= z < n implies
                get_flow(f2, w, z) == get_flow(f, w, z) + (if w == a && z == b { d } else { 0int }) by {
                fm_get(fl, n, w, z);
                fm_get(fl2, n, w, z);
            }
            let c1 = if u == b { d } else { 0int };
            let e1 = |w: int| if w == a { c1 } else { 0int };
            let h1 = |w: int| get_flow(f, w, u);
            let h2 = |w: int| get_flow(f2, w, u);
            assert forall |w: int| 0 <= w < n implies #[trigger] h2(w) == h1(w) + e1(w) by {}
            ssum_add(n, h1, e1, h2);
            ssum_point(n, e1, a, c1);
            let c2 = if u == a { d } else { 0int };
            let e2 = |v: int| if v == b { c2 } else { 0int };
            let o1 = |v: int| get_flow(f, u, v);
            let o2 = |v: int| get_flow(f2, u, v);
            assert forall |v: int| 0 <= v < n implies #[trigger] o2(v) == o1(v) + e2(v) by {}
            ssum_add(n, o1, e2, o2);
            ssum_point(n, e2, b, c2);
        }
    }

    proof fn final_max(g: Seq<Seq<(int, int)>>, fl: Seq<Seq<i64>>, cap: Seq<Seq<i64>>, vis: Seq<bool>, s: int, t: int)
        requires wf(g), capacities_bounded(g), shaped(fl, g.len() as int), shaped(cap, g.len() as int),
            vis.len() == g.len(),
            forall |u: int, v: int| 0 <= u < g.len() && 0 <= v < g.len() ==>
                (#[trigger] cap[u][v] == capf(g, u, v) && 0 <= fl[u][v] <= cap[u][v]),
            0 <= s < g.len(), 0 <= t < g.len(), s != t,
            forall |u: int| 0 <= u < g.len() && u != s && u != t ==> net(g.len() as int, fm(fl, g.len() as int), u) == 0,
            vis[s], !vis[t],
            forall |u: int, v: int| 0 <= u < g.len() && 0 <= v < g.len() && vis[u]
                && (fl[u][v] < #[trigger] cap[u][v] || fl[v][u] > 0) ==> vis[v]
        ensures
            is_max_flow(g, fm(fl, g.len() as int), s, t),
            flow_val(g, fm(fl, g.len() as int), s) == -net(g.len() as int, fm(fl, g.len() as int), s)
    {
        let n = g.len() as int;
        let f = fm(fl, n);
        assert forall |u: int, v: int| 0 <= u < n && 0 <= v < n implies
            0 <= #[trigger] get_flow(f, u, v) && get_flow(f, u, v) <= capf(g, u, v) by { assert(cap[u][v] == capf(g, u, v)); fm_get(fl, n, u, v); }
        assert(feas(g, f));
        assert forall |u: int, v: int| f.dom().contains((u, v)) implies 0 <= u < g.len() && 0 <= v < g.len() by {}
        feas_respects(g, f);
        assert forall |u: int| 0 <= u < n && u != s && u != t implies
            total_flow_in(g, f, u) == total_flow_out(g, f, u) by {
            assert(net(n, f, u) == 0);
            in_eq(g, f, u, n);
            out_eq(g, f, u);
        }
        assert forall |u: int, v: int| #[trigger] f.dom().contains((u, v)) implies f[(u, v)] >= 0 by {
            fm_get(fl, n, u, v);
        }
        assert(is_valid_flow(g, f, s, t));
        in_eq(g, f, s, n);
        out_eq(g, f, s);
        let sset = |u: int| 0 <= u < n && vis[u];
        cut_eq(n, f, sset, s, t);
        assert forall |h: FlowMap| #[trigger] is_valid_flow(g, h, s, t) implies flow_val(g, f, s) >= flow_val(g, h, s) by {
            valid_feas(g, h, s, t);
            assert forall |u: int| 0 <= u < n && u != s && u != t implies net(n, h, u) == 0 by {
                in_eq(g, h, u, n);
                out_eq(g, h, u);
            }
            in_eq(g, h, s, n);
            out_eq(g, h, s);
            cut_eq(n, h, sset, s, t);
            assert forall |u: int, v: int| 0 <= u < n && 0 <= v < n && sset(u) && !sset(v) implies dd(h, u, v) <= dd(f, u, v) by {
                fm_get(fl, n, u, v);
                fm_get(fl, n, v, u);
                assert(!(fl[u][v] < cap[u][v]));
                assert(!(fl[v][u] > 0));
            }
            cut_mono(n, f, h, sset);
        }
    }

    proof fn bfs_push(n: int, ff: Seq<Seq<i64>>, cc: Seq<Seq<i64>>, s: int,
        vis: Seq<bool>, par: Seq<usize>, rk: Seq<usize>, q: Seq<usize>, head: int, v: int)
        requires bfs_ok(n, ff, cc, s, vis, par, rk, q, head), head < q.len(), 0 <= v < n, !vis[v],
            n <= usize::MAX, q.len() < n,
            resid(ff, cc, q[head] as int, v)
        ensures bfs_ok(n, ff, cc, s, vis.update(v, true), par.update(v, q[head]),
            rk.update(v, q.len() as usize), q.push(v as usize), head)
    {
        let u = q[head] as int;
        let vis2 = vis.update(v, true);
        let par2 = par.update(v, q[head]);
        let rk2 = rk.update(v, q.len() as usize);
        let q2 = q.push(v as usize);
        assert(vis[u] && rk[u] == head);
        assert(v != s);
        assert forall |i: int| 0 <= i < q2.len() implies
            (#[trigger] q2[i]) < n && vis2[q2[i] as int] && rk2[q2[i] as int] == i by {
            if i < q.len() { assert(q[i] < n && vis[q[i] as int]); } else { assert(q2[i] == v as usize); }
        }
        assert forall |w: int| 0 <= w < n && #[trigger] vis2[w] implies
            rk2[w] < q2.len() && q2[rk2[w] as int] == w by {
            if w != v { assert(vis[w]); } else { assert(q2[q.len() as int] == v as usize); }
        }
        assert forall |w: int| 0 <= w < n && #[trigger] vis2[w] && w != s implies
            par2[w] < n && vis2[par2[w] as int] && rk2[par2[w] as int] < rk2[w]
            && resid(ff, cc, par2[w] as int, w) by {
            if w != v { assert(vis[w]); assert(vis[par[w] as int]); }
        }
        assert forall |i: int, w: int| 0 <= i < head && 0 <= w < n && #[trigger] resid(ff, cc, q2[i] as int, w)
            implies vis2[w] by {
            assert(q2[i] == q[i]);
        }
    }

    proof fn card_bound(vs: Set<int>, n: int)
        requires n >= 0, forall |x: int| vs.contains(x) ==> 0 <= x < n
        ensures vs.finite(), vs.len() <= n
    {
        vstd::set_lib::lemma_int_range(0, n);
        assert(vs.subset_of(vstd::set_lib::set_int_range(0, n)));
        vstd::set_lib::lemma_len_subset(vs, vstd::set_lib::set_int_range(0, n));
    }

    proof fn zero_net(fl: Seq<Seq<i64>>, n: int)
        requires shaped(fl, n), forall |a: int, b: int| 0 <= a < n && 0 <= b < n ==> #[trigger] fl[a][b] == 0
        ensures forall |u: int| 0 <= u < n ==> #[trigger] net(n, fm(fl, n), u) == 0
    {
        let f = fm(fl, n);
        assert forall |u: int| 0 <= u < n implies #[trigger] net(n, f, u) == 0 by {
            let z1 = |v: int| get_flow(f, v, u);
            let z2 = |v: int| get_flow(f, u, v);
            assert forall |v: int| 0 <= v < n implies #[trigger] z1(v) == 0 by { fm_get(fl, n, v, u); }
            assert forall |v: int| 0 <= v < n implies #[trigger] z2(v) == 0 by { fm_get(fl, n, u, v); }
            lemma_ssum_zero(n, z1);
            lemma_ssum_zero(n, z2);
        }
    }

    proof fn mat_feas(g: Seq<Seq<(int, int)>>, fl: Seq<Seq<i64>>, cap: Seq<Seq<i64>>)
        requires shaped(fl, g.len() as int), shaped(cap, g.len() as int),
            forall |u: int, v: int| 0 <= u < g.len() && 0 <= v < g.len() ==>
                (#[trigger] cap[u][v] == capf(g, u, v) && 0 <= fl[u][v] <= cap[u][v])
        ensures feas(g, fm(fl, g.len() as int))
    {
        let n = g.len() as int;
        assert forall |u: int, v: int| 0 <= u < n && 0 <= v < n implies
            0 <= #[trigger] get_flow(fm(fl, n), u, v) && get_flow(fm(fl, n), u, v) <= capf(g, u, v) by {
            assert(cap[u][v] == capf(g, u, v));
            fm_get(fl, n, u, v);
        }
    }
