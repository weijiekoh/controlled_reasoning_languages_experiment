    {
        let n: usize = graph.adj.len();
        let mut done: Vec<bool> = Vec::new();
        let mut init: usize = 0;
        while init < n
            invariant
                init <= n,
                done@.len() == init,
                forall |x: int| 0 <= x < init ==> !done@[x],
            decreases n - init,
        {
            done.push(false);
            init += 1;
        }
        let mut order: Vec<usize> = Vec::new();
        let mut stuck: bool = false;
        proof { lemma_view_idx(graph); }
        while order.len() < n && !stuck
            invariant
                n == graph.adj.len(),
                done@.len() == n,
                graph.well_formed(),
                inv_order(graph.view(), done@, order@),
                order@.len() <= n,
                stuck ==> forall |x: int| 0 <= x < n && !done@[x] ==> !ready_spec(graph.view(), done@, x),
            decreases n - order.len(), if stuck { 0int } else { 1int },
        {
            let mut found: Option<usize> = None;
            let mut v: usize = 0;
            while v < n
                invariant
                    v <= n,
                    n == graph.adj.len(),
                    done@.len() == n,
                    graph.well_formed(),
                    found.is_none() ==> forall |x: int| 0 <= x < v && !done@[x] ==> !ready_spec(graph.view(), done@, x),
                    found.is_some() ==> (found.unwrap() < n && !done@[found.unwrap() as int]
                        && ready_spec(graph.view(), done@, found.unwrap() as int)),
                decreases n - v,
            {
                if found.is_none() && !done[v] {
                    match find_pred(graph, &done, v) {
                        Some((u, k)) => {
                            proof {
                                assert(!ready_spec(graph.view(), done@, v as int)) by {
                                    assert(graph.view()[u as int][k as int] == graph.adj[u as int][k as int] as int);
                                }
                            }
                        }
                        None => {
                            found = Some(v);
                        }
                    }
                }
                v += 1;
            }
            match found {
                Some(c) => {
                    let ghost od = done@;
                    let ghost oo = order@;
                    proof { assert(!od[c as int]); }
                    order.push(c);
                    done.set(c, true);
                    proof { lemma_step(graph, od, oo, c); }
                }
                None => {
                    stuck = true;
                }
            }
        }

        // Find an unprocessed node, if any.
        let mut k: usize = 0;
        let mut missing: Option<usize> = None;
        while k < n
            invariant
                k <= n,
                n == graph.adj.len(),
                done@.len() == n,
                missing.is_none() ==> forall |x: int| 0 <= x < k ==> done@[x],
                missing.is_some() ==> (missing.unwrap() < n && !done@[missing.unwrap() as int]),
            decreases n - k,
        {
            if missing.is_none() && !done[k] {
                missing = Some(k);
            }
            k += 1;
        }

        match missing {
            None => {
                proof {
                    assert forall |x: int| 0 <= x < graph.view().len() implies done@[x] by {
                        assert(x < n);
                    }
                    lemma_no_cycle(graph, done@, order@);
                    lemma_topo(graph, done@, order@);
                }
                return Some(order);
            }
            Some(s0) => {
                proof {
                    if !stuck {
                        // loop ended because order is full: every node is covered, contradiction
                        assert(order@.len() == n);
                        assert(forall |i: int| 0 <= i < order@.len() ==> (order@[i] as int) < n);
                        assert(forall |i: int| 0 <= i < order@.len() ==> order@[i] as int != s0 as int) by {
                            assert(forall |i: int| 0 <= i < order@.len() ==> done@[order@[i] as int]);
                            assert(!done@[s0 as int]);
                            assert forall |i: int| 0 <= i < order@.len() implies order@[i] as int != s0 as int by {
                                assert(done@[order@[i] as int]);
                            }
                        }
                        lemma_cover(order@, n as int, s0 as int);
                        assert(false);
                    }
                }
                let mut walk: Vec<usize> = Vec::new();
                walk.push(s0);
                let mut cur: usize = s0;
                loop
                    invariant
                        n == graph.adj.len(),
                        done@.len() == n,
                        graph.well_formed(),
                        walk@.len() >= 1,
                        walk@.len() <= n,
                        walk@.no_duplicates(),
                        forall |i: int| 0 <= i < walk@.len() ==> (walk@[i] as int) < n,
                        forall |k: int| 0 <= k < walk@.len() - 1 ==> has_edge(graph.view(), walk@[k + 1] as int, #[trigger] walk@[k] as int),
                        walk@[walk@.len() - 1] == cur,
                        !done@[cur as int],
                        forall |x: int| 0 <= x < n && !done@[x] ==> !ready_spec(graph.view(), done@, x),
                    decreases n - walk.len(),
                {
                    match find_pred(graph, &done, cur) {
                        Some((p, kk)) => {
                            match find_index(&walk, p) {
                                Some(a) => {
                                    proof {
                                        assert(has_edge(graph.view(), walk@[a as int] as int, cur as int)) by {
                                            assert(graph.view()[p as int][kk as int] == graph.adj[p as int][kk as int] as int);
                                        }
                                        lemma_cycle_build(graph, walk@, a as int);
                                    }
                                    return None;
                                }
                                None => {
                                    proof {
                                        assert(has_edge(graph.view(), p as int, cur as int)) by {
                                            assert(graph.view()[p as int][kk as int] == graph.adj[p as int][kk as int] as int);
                                        }
                                    }
                                    walk.push(p);
                                    cur = p;
                                    proof { lemma_bound_u(walk@, n as int); }
                                }
                            }
                        }
                        None => {
                            proof { assert(false); }
                            return None;
                        }
                    }
                }
            }
        }
    }
