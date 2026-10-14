    pub open spec fn ssum(n: int, h: spec_fn(int) -> int) -> int
        decreases n
    {
        if n <= 0 { 0 } else { ssum(n - 1, h) + h(n - 1) }
    }

    pub open spec fn wf(g: Seq<Seq<(int, int)>>) -> bool {
        &&& forall |u: int, i: int|
            0 <= u < g.len() && 0 <= i < g[u].len()
            ==> 0 <= #[trigger] g[u][i].0 < g.len()
        &&& forall |u: int, i: int, j: int|
            0 <= u < g.len()
            && 0 <= i < g[u].len()
            && 0 <= j < g[u].len()
            && i != j
            ==> #[trigger] g[u][i].0 != #[trigger] g[u][j].0
    }

    pub open spec fn has_edge(g: Seq<Seq<(int, int)>>, u: int, v: int) -> bool {
        exists |i: int| 0 <= u < g.len() && 0 <= i < g[u].len() && #[trigger] g[u][i].0 == v
    }

    pub open spec fn eidx(g: Seq<Seq<(int, int)>>, u: int, v: int) -> int {
        choose |i: int| 0 <= u < g.len() && 0 <= i < g[u].len() && #[trigger] g[u][i].0 == v
    }

    pub open spec fn capf(g: Seq<Seq<(int, int)>>, u: int, v: int) -> int {
        if has_edge(g, u, v) { g[u][eidx(g, u, v)].1 } else { 0 }
    }

    pub open spec fn feas(g: Seq<Seq<(int, int)>>, f: FlowMap) -> bool {
        forall |u: int, v: int| 0 <= u < g.len() && 0 <= v < g.len()
            ==> 0 <= #[trigger] get_flow(f, u, v) && get_flow(f, u, v) <= capf(g, u, v)
    }

    pub open spec fn inn(n: int, f: FlowMap, u: int) -> int {
        ssum(n, |v: int| get_flow(f, v, u))
    }
    pub open spec fn outn(n: int, f: FlowMap, u: int) -> int {
        ssum(n, |v: int| get_flow(f, u, v))
    }
    pub open spec fn net(n: int, f: FlowMap, u: int) -> int {
        inn(n, f, u) - outn(n, f, u)
    }

    pub open spec fn dd(f: FlowMap, u: int, v: int) -> int {
        get_flow(f, u, v) - get_flow(f, v, u)
    }

    pub open spec fn cutval(n: int, f: FlowMap, sset: spec_fn(int) -> bool) -> int {
        ssum(n, |u: int| ssum(n, |v: int| if sset(u) && !sset(v) { dd(f, u, v) } else { 0 }))
    }

    pub open spec fn fm(fl: Seq<Seq<i64>>, n: int) -> FlowMap {
        Map::new(|p: (int, int)| 0 <= p.0 < n && 0 <= p.1 < n, |p: (int, int)| fl[p.0][p.1] as int)
    }

    pub open spec fn shaped<T>(m: Seq<Seq<T>>, n: int) -> bool {
        m.len() == n && forall |i: int| 0 <= i < n ==> (#[trigger] m[i]).len() == n
    }

    pub open spec fn amt(fl: Seq<Seq<i64>>, cap: Seq<Seq<i64>>, p: int, w: int) -> int {
        if fl[p][w] < cap[p][w] { cap[p][w] - fl[p][w] } else { fl[w][p] as int }
    }

    pub open spec fn mv(m: Seq<Vec<i64>>) -> Seq<Seq<i64>> { m.map_values(|r: Vec<i64>| r@) }

    pub open spec fn resid(ff: Seq<Seq<i64>>, cc: Seq<Seq<i64>>, u: int, v: int) -> bool {
        ff[u][v] < cc[u][v] || ff[v][u] > 0
    }

    pub open spec fn bfs_ok(n: int, ff: Seq<Seq<i64>>, cc: Seq<Seq<i64>>, s: int,
        vis: Seq<bool>, par: Seq<usize>, rk: Seq<usize>, q: Seq<usize>, head: int) -> bool
    {
        &&& 0 <= s < n
        &&& vis.len() == n && par.len() == n && rk.len() == n
        &&& 0 <= head <= q.len()
        &&& vis[s]
        &&& forall |i: int| 0 <= i < q.len() ==>
                (#[trigger] q[i]) < n && vis[q[i] as int] && rk[q[i] as int] == i
        &&& forall |v: int| 0 <= v < n && #[trigger] vis[v] ==>
                rk[v] < q.len() && q[rk[v] as int] == v
        &&& forall |v: int| 0 <= v < n && #[trigger] vis[v] && v != s ==>
                par[v] < n && vis[par[v] as int] && rk[par[v] as int] < rk[v]
                && resid(ff, cc, par[v] as int, v)
        &&& forall |i: int, v: int| 0 <= i < head && 0 <= v < n && #[trigger] resid(ff, cc, q[i] as int, v)
                ==> vis[v]
    }

    fn set2(m: &mut Vec<Vec<i64>>, a: usize, b: usize, x: i64)
        requires a < old(m).len(), b < old(m)[a as int].len()
        ensures m.len() == old(m).len(),
            mv(m@) == mv(old(m)@).update(a as int, mv(old(m)@)[a as int].update(b as int, x))
    {
        let ghost o = mv(m@);
        let mut row: Vec<i64> = Vec::new();
        m.set_and_swap(a, &mut row);
        row.set(b, x);
        m.set_and_swap(a, &mut row);
        proof { assert(mv(m@) =~= o.update(a as int, o[a as int].update(b as int, x))); }
    }

    fn mkvec<T: Copy>(n: usize, x: T) -> (v: Vec<T>)
        ensures v.len() == n, forall |i: int| 0 <= i < n ==> v[i] == x
    {
        let mut v: Vec<T> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant i <= n, v.len() == i, forall |k: int| 0 <= k < i ==> v[k] == x,
            decreases n - i
        {
            v.push(x);
            i += 1;
        }
        v
    }
