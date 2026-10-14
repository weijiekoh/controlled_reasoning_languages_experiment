    {
        let n = graph.adj.len();
        let ghost g = graph.view();
        proof { assert(wf(g)); assert(g.len() == n as int); }
        // ---- capacity matrix
        let mut cap: Vec<Vec<i64>> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n, cap.len() == i,
                forall |a: int| 0 <= a < i ==> (#[trigger] cap[a]).len() == n,
                forall |a: int, b: int| 0 <= a < i && 0 <= b < n ==> #[trigger] cap[a]@[b] == 0,
            decreases n - i
        {
            cap.push(mkvec(n, 0i64));
            i += 1;
        }
        let mut u: usize = 0;
        while u < n
            invariant
                u <= n, cap.len() == n, n == g.len(), n == graph.adj.len(), wf(g), g == graph.view(),
                shaped(mv(cap@), n as int),
                forall |a: int, b: int| 0 <= a < u && 0 <= b < n ==> #[trigger] mv(cap@)[a][b] == capf(g, a, b),
                forall |a: int, b: int| u <= a < n && 0 <= b < n ==> #[trigger] mv(cap@)[a][b] == 0,
            decreases n - u
        {
            let deg = graph.adj[u].len();
            proof { assert(g[u as int].len() == graph.adj[u as int].len()); }
            let mut j: usize = 0;
            while j < deg
                invariant
                    j <= deg, deg == g[u as int].len(), u < n, cap.len() == n, n == g.len(), n == graph.adj.len(), g == graph.view(),
                    deg == graph.adj[u as int].len(),
                    shaped(mv(cap@), n as int),
                    forall |a: int, b: int| 0 <= a < u && 0 <= b < n ==> #[trigger] mv(cap@)[a][b] == capf(g, a, b),
                    forall |a: int, b: int| u < a < n && 0 <= b < n ==> #[trigger] mv(cap@)[a][b] == 0,
                    forall |i: int| 0 <= i < j ==> mv(cap@)[u as int][#[trigger] g[u as int][i].0] == g[u as int][i].1,
                    forall |b: int| 0 <= b < n && !(exists |i: int| 0 <= i < j && #[trigger] g[u as int][i].0 == b)
                        ==> #[trigger] mv(cap@)[u as int][b] == 0,
                    wf(g),
                decreases deg - j
            {
                let (v, c) = graph.adj[u][j];
                proof {
                    assert(g[u as int][j as int].0 == v as int);
                    assert(g[u as int][j as int].1 == c as int);
                    assert(0 <= g[u as int][j as int].0 < g.len());
                }
                let ghost old = mv(cap@);
                proof { assert(cap[u as int]@ == mv(cap@)[u as int]); assert(mv(cap@)[u as int].len() == n); }
                set2(&mut cap, u, v, c);
                proof {
                    let nw = mv(cap@);
                    assert forall |a: int, b: int| 0 <= a < n && 0 <= b < n implies
                        #[trigger] nw[a][b] == (if a == u as int && b == v as int { c as int } else { old[a][b] as int }) by {}
                    assert(shaped(nw, n as int)) by {
                        assert forall |a: int| 0 <= a < n implies (#[trigger] nw[a]).len() == n by {}
                    }
                    assert forall |i: int| 0 <= i < j + 1 implies
                        nw[u as int][#[trigger] g[u as int][i].0] == g[u as int][i].1 by {
                        if i < j {
                            assert(g[u as int][i].0 != g[u as int][j as int].0);
                        }
                    }
                    assert forall |b: int| 0 <= b < n && !(exists |i: int| 0 <= i < j + 1 && #[trigger] g[u as int][i].0 == b)
                        implies #[trigger] nw[u as int][b] == 0 by {
                        assert(b != v as int);
                        assert(!(exists |i: int| 0 <= i < j && #[trigger] g[u as int][i].0 == b)) by {
                            if exists |i: int| 0 <= i < j && #[trigger] g[u as int][i].0 == b {
                                let i = choose |i: int| 0 <= i < j && #[trigger] g[u as int][i].0 == b;
                                assert(0 <= i < j + 1);
                            }
                        }
                    }
                }
                j += 1;
            }
            proof {
                assert forall |b: int| 0 <= b < n implies #[trigger] mv(cap@)[u as int][b] == capf(g, u as int, b) by {
                    if has_edge(g, u as int, b) {
                        eidx_ok(g, u as int, b);
                        let i = eidx(g, u as int, b);
                        assert(mv(cap@)[u as int][g[u as int][i].0] == g[u as int][i].1);
                    } else {
                        assert(!(exists |i: int| 0 <= i < deg && #[trigger] g[u as int][i].0 == b));
                    }
                }
            }
            u += 1;
        }
        // ---- flow matrix
        let mut fl: Vec<Vec<i64>> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n, fl.len() == i,
                forall |a: int| 0 <= a < i ==> (#[trigger] fl[a]).len() == n,
                forall |a: int, b: int| 0 <= a < i && 0 <= b < n ==> #[trigger] fl[a]@[b] == 0,
            decreases n - i
        {
            fl.push(mkvec(n, 0i64));
            i += 1;
        }
        let mut flow: i64 = 0;
        proof {
            assert(shaped(mv(fl@), n as int)) by {
                assert forall |a: int| 0 <= a < n implies (#[trigger] mv(fl@)[a]).len() == n by {}
            }
            assert forall |a: int, b: int| 0 <= a < n && 0 <= b < n implies #[trigger] mv(fl@)[a][b] == 0 by {}
            zero_net(mv(fl@), n as int);
            assert forall |a: int, b: int| 0 <= a < n && 0 <= b < n implies #[trigger] mv(cap@)[a][b] >= 0 by { capf_bounds(g, a, b); }
            assert(net(n as int, fm(mv(fl@), n as int), s as int) == 0);
        }
        loop
            invariant
                n == g.len(), n <= 1000, wf(g), capacities_bounded(g), s < n, t < n, s != t,
                g == graph.view(),
                cap.len() == n, fl.len() == n,
                shaped(mv(cap@), n as int), shaped(mv(fl@), n as int),
                forall |a: int, b: int| 0 <= a < n && 0 <= b < n ==>
                    (#[trigger] mv(cap@)[a][b] == capf(g, a, b) && 0 <= mv(fl@)[a][b] <= mv(cap@)[a][b]),
                forall |u: int| 0 <= u < n && u != s && u != t ==> #[trigger] net(n as int, fm(mv(fl@), n as int), u) == 0,
                flow as int == -net(n as int, fm(mv(fl@), n as int), s as int),
                flow <= 100_000_000,
            decreases 100_000_000 - flow
        {
            let ghost ff = mv(fl@);
            let ghost cc = mv(cap@);
            // ---- BFS
            let mut visited: Vec<bool> = mkvec(n, false);
            let mut parent: Vec<usize> = mkvec(n, 0usize);
            let mut rank: Vec<usize> = mkvec(n, 0usize);
            let mut q: Vec<usize> = Vec::new();
            visited.set(s, true);
            q.push(s);
            let mut head: usize = 0;
            let ghost mut vs: Set<int> = Set::empty().insert(s as int);
            proof {
                assert(bfs_ok(n as int, ff, cc, s as int, visited@, parent@, rank@, q@, 0)) by {
                    assert forall |v: int| 0 <= v < n && #[trigger] visited@[v] implies
                        rank@[v] < q@.len() && q@[rank@[v] as int] == v by {
                        if v != s as int { }
                    }
                }
            }
            while head < q.len()
                invariant
                    n == g.len(), n <= 1000, s < n, ff == mv(fl@), cc == mv(cap@), cap.len() == n, fl.len() == n,
                    shaped(ff, n as int), shaped(cc, n as int),
                    bfs_ok(n as int, ff, cc, s as int, visited@, parent@, rank@, q@, head as int),
                    forall |x: int| vs.contains(x) <==> (0 <= x < n && visited@[x]),
                    q.len() == vs.len(), vs.finite(),
                decreases n - head
            {
                proof {
                    assert forall |x: int| vs.contains(x) implies 0 <= x < n as int by {}
                    card_bound(vs, n as int);
                }
                let u = q[head];
                let mut v: usize = 0;
                proof { assert(visited@[u as int] && rank@[u as int] == head); }
                while v < n
                    invariant
                        n == g.len(), n <= 1000, s < n, ff == mv(fl@), cc == mv(cap@),
                        cap.len() == n, fl.len() == n,
                        shaped(ff, n as int), shaped(cc, n as int),
                        v <= n, head < q.len(), u == q[head as int], u < n,
                        bfs_ok(n as int, ff, cc, s as int, visited@, parent@, rank@, q@, head as int),
                        forall |x: int| vs.contains(x) <==> (0 <= x < n && visited@[x]),
                        q.len() == vs.len(), vs.finite(),
                        forall |x: int| 0 <= x < v && resid(ff, cc, u as int, x) ==> visited@[x],
                    decreases n - v
                {
                    proof {
                        assert forall |x: int| vs.contains(x) implies 0 <= x < n as int by {}
                        card_bound(vs, n as int);
                    }
                    proof {
                        assert(ff[u as int].len() == n && ff[v as int].len() == n && cc[u as int].len() == n && cc[v as int].len() == n);
                        assert(fl[u as int]@ == ff[u as int] && fl[v as int]@ == ff[v as int]);
                        assert(cap[u as int]@ == cc[u as int] && cap[v as int]@ == cc[v as int]);
                    }
                    if !visited[v] && (fl[u][v] < cap[u][v] || fl[v][u] > 0) {
                        proof {
                            assert(resid(ff, cc, u as int, v as int));
                            assert(!vs.contains(v as int));
                            assert(vs.insert(v as int).len() == vs.len() + 1);
                            assert forall |x: int| vs.contains(x) implies 0 <= x < n as int by {}
                            card_bound(vs.insert(v as int), n as int);
                            bfs_push(n as int, ff, cc, s as int, visited@, parent@, rank@, q@, head as int, v as int);
                            vs = vs.insert(v as int);
                        }
                        let ql = q.len();
                        visited.set(v, true);
                        parent.set(v, u);
                        rank.set(v, ql);
                        q.push(v);
                    }
                    v += 1;
                }
                head += 1;
            }
            proof {
                assert(head == q.len());
            }
            if !visited[t] {
                proof {
                    assert forall |a: int, b: int| 0 <= a < n && 0 <= b < n && visited@[a]
                        && (#[trigger] ff[a][b] < cc[a][b] || ff[b][a] > 0) implies visited@[b] by {
                        assert(rank@[a] < q@.len() && q@[rank@[a] as int] == a);
                        assert(resid(ff, cc, q@[rank@[a] as int] as int, b));
                    }
                    final_max(g, ff, cc, visited@, s as int, t as int);
                    let f = fm(ff, n as int);
                    assert(is_max_flow(g, f, s as int, t as int) && flow_val(g, f, s as int) == flow as int);
                    assert(exists |f2: FlowMap| #[trigger] is_max_flow(graph.view(), f2, s as int, t as int) && flow_val(graph.view(), f2, s as int) == flow as int);
                }
                return flow;
            }
            // ---- augmenting path
            proof { assert(visited@[t as int]); }
            proof {
                assert forall |a: int, b: int| 0 <= a < n && 0 <= b < n implies 0 <= #[trigger] ff[a][b] <= cc[a][b] by {
                    assert(mv(cap@)[a][b] == capf(g, a, b) && 0 <= mv(fl@)[a][b] <= mv(cap@)[a][b]);
                }
            }
            let mut path: Vec<usize> = Vec::new();
            path.push(t);
            let mut cur: usize = t;
            let mut delta: i64 = 1_000_000;
            while cur != s
                invariant
                    n == g.len(), s < n, t < n, s != t, ff == mv(fl@), cc == mv(cap@),
                    shaped(ff, n as int), shaped(cc, n as int),
                    forall |a: int, b: int| 0 <= a < n && 0 <= b < n ==> 0 <= #[trigger] ff[a][b] <= cc[a][b],
                    bfs_ok(n as int, ff, cc, s as int, visited@, parent@, rank@, q@, head as int),
                    cur < n, visited@[cur as int], path.len() >= 1, path[0] == t, path[path.len() - 1] == cur,
                    0 < delta <= 1_000_000,
                    forall |i: int| 0 <= i < path.len() ==> (#[trigger] path[i]) < n,
                    forall |i: int| 0 <= i < path.len() - 1 ==>
                        path[i + 1] == parent[path[i] as int]
                        && rank[path[i + 1] as int] < rank[path[i] as int]
                        && delta as int <= amt(ff, cc, path[i + 1] as int, path[i] as int),
                decreases rank[cur as int]
            {
                let p = parent[cur];
                let ghost op = path@;
                let ghost od = delta as int;
                proof { assert(visited@[cur as int] && cur != s); }
                let a: i64 = if fl[p][cur] < cap[p][cur] { cap[p][cur] - fl[p][cur] } else { fl[cur][p] };
                proof {
                    assert(resid(ff, cc, p as int, cur as int));
                    assert(a as int == amt(ff, cc, p as int, cur as int));
                }
                if a < delta { delta = a; }
                proof { assert(delta as int <= od); assert(rank[p as int] < rank[cur as int]); }
                path.push(p);
                cur = p;
                proof {
                    assert forall |i: int| 0 <= i < path.len() - 1 implies
                        path[i + 1] == parent[path[i] as int]
                        && rank[path[i + 1] as int] < rank[path[i] as int]
                        && delta as int <= amt(ff, cc, path[i + 1] as int, path[i] as int) by {
                        if i < op.len() - 1 {
                            assert(path[i] == op[i] && path[i + 1] == op[i + 1]);
                            assert(path[i + 1] == parent[path[i] as int]);
                            assert(rank[path[i + 1] as int] < rank[path[i] as int]);
                            assert(delta as int <= amt(ff, cc, path[i + 1] as int, path[i] as int));
                        } else {
                            assert(path[i] == op[op.len() - 1]);
                            assert(path[i + 1] == p);
                            assert(path[i + 1] == parent[path[i] as int]);
                            assert(rank[path[i + 1] as int] < rank[path[i] as int]);
                            assert(delta as int <= amt(ff, cc, path[i + 1] as int, path[i] as int));
                        }
                    }
                }
            }
            let k = path.len();
            // ---- augment
            let ghost fl0 = mv(fl@);
            let mut j: usize = 0;
            while j + 1 < k
                invariant
                    n == g.len(), n <= 1000, s < n, t < n, s != t, cc == mv(cap@), fl0 == ff,
                    cap.len() == n, fl.len() == n, k == path.len(),
                    shaped(cc, n as int), shaped(mv(fl@), n as int),
                    bfs_ok(n as int, ff, cc, s as int, visited@, parent@, rank@, q@, head as int),
                    0 < delta <= 1_000_000, j < k, k >= 2, path[0] == t, path[k as int - 1] == s,
                    forall |i: int| 0 <= i < path.len() ==> (#[trigger] path[i]) < n,
                    forall |i: int| 0 <= i < path.len() - 1 ==>
                        path[i + 1] == parent[path[i] as int]
                        && rank[path[i + 1] as int] < rank[path[i] as int]
                        && delta as int <= amt(ff, cc, path[i + 1] as int, path[i] as int),
                    forall |a: int, b: int| 0 <= a < n && 0 <= b < n ==> 0 <= #[trigger] ff[a][b] <= cc[a][b],
                    forall |a: int, b: int| 0 <= a < n && 0 <= b < n ==> 0 <= #[trigger] mv(fl@)[a][b] <= cc[a][b],
                    forall |u: int| 0 <= u < n ==> #[trigger] net(n as int, fm(mv(fl@), n as int), u)
                        == net(n as int, fm(ff, n as int), u)
                            - (if u == path[j as int] as int { delta as int } else { 0int })
                            + (if u == t as int { delta as int } else { 0int }),
                    forall |a: int, b: int| 0 <= a < n && 0 <= b < n && #[trigger] mv(fl@)[a][b] != ff[a][b] ==>
                        rank[a] >= rank[path[j as int] as int] && rank[b] >= rank[path[j as int] as int],
                decreases k - j
            {
                let w = path[j];
                let p = path[j + 1];
                let ghost cf = mv(fl@);
                proof {
                    assert(path[j as int + 1] == parent[path[j as int] as int]);
                    assert(rank[p as int] < rank[w as int]);
                    assert(p != w);
                    assert(cf[p as int][w as int] == ff[p as int][w as int]);
                    assert(cf[w as int][p as int] == ff[w as int][p as int]);
                }
                let fpw = fl[p][w];
                if fpw < cap[p][w] {
                    proof {
                        assert(delta as int <= amt(ff, cc, p as int, w as int));
                        upd_net(cf, mv(fl@).update(p as int, mv(fl@)[p as int].update(w as int, (fpw + delta) as i64)), n as int, p as int, w as int, (fpw + delta) as i64);
                    }
                    set2(&mut fl, p, w, fpw + delta);
                } else {
                    let fwp = fl[w][p];
                    proof {
                        assert(delta as int <= amt(ff, cc, p as int, w as int));
                        upd_net(cf, mv(fl@).update(w as int, mv(fl@)[w as int].update(p as int, (fwp - delta) as i64)), n as int, w as int, p as int, (fwp - delta) as i64);
                    }
                    set2(&mut fl, w, p, fwp - delta);
                }
                proof {
                    let nf = mv(fl@);
                    assert forall |a: int, b: int| 0 <= a < n && 0 <= b < n implies
                        0 <= #[trigger] nf[a][b] <= cc[a][b] by {}
                }
                j += 1;
            }
            proof {
                assert(path[j as int] == s);
                let nf = mv(fl@);
                assert(feas(g, fm(nf, n as int))) by { mat_feas(g, nf, cc); }
                val_bound(g, fm(nf, n as int), s as int);
            }
            flow = flow + delta;
        }
    }
