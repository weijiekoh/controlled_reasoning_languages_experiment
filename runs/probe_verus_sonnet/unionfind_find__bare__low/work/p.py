s=open('unionfind_find.rs').read()
h='''
        pub proof fn lemma_root(&self, i: usize)
            requires self.is_valid(), i < self.parent.len(),
            ensures self.spec_find(i) < self.parent.len(),
                self.spec_find(self.spec_find(i)) == self.spec_find(i),
                self.spec_find(i) == i || self.rank[i as int] < self.rank[self.spec_find(i) as int],
            decreases self.measure(i)
        {
            let p = self.parent[i as int];
            if p != i {
                self.lemma_root(p);
            }
        }

        pub proof fn lemma_upd(&self, o: &UnionFind, i: usize, j: usize)
            requires self.is_valid(), i < self.parent.len(), j < self.parent.len(),
                o.parent.len() == self.parent.len(),
                o.rank == self.rank,
                o.parent == self.parent.update(i as int, self.spec_find(i)),
            ensures o.spec_find(j) == self.spec_find(j),
            decreases self.measure(j)
        {
            self.lemma_root(i);
            let r = self.spec_find(i);
            let p = self.parent[j as int];
            if j == i {
                if r != i {
                    self.lemma_root(r);
                    assert(o.parent[r as int] == self.parent[r as int]);
                }
            } else if p != j {
                self.lemma_upd(o, i, p);
            }
        }

        pub fn find_rec(&mut self, i: usize) -> (root: usize)
            requires old(self).is_valid(), i < old(self).parent.len(),
            ensures
                self.is_valid(),
                root == self.spec_find(i),
                forall|j: usize| 0 <= j < self.parent.len() ==>
                    #[trigger] self.spec_find(j) == old(self).spec_find(j),
                self.parent.len() == old(self).parent.len(),
                self.rank == old(self).rank,
            decreases old(self).measure(i)
        {
            let p = self.parent[i];
            if p == i {
                return i;
            }
            proof { assert(self.rank[i as int] < self.rank[p as int]); }
            let ghost s0 = *self;
            let r = self.find_rec(p);
            let ghost s1 = *self;
            proof {
                s0.lemma_root(i);
                s0.lemma_root(p);
                assert(s1.spec_find(p) == s0.spec_find(p));
                assert(r == s0.spec_find(i));
            }
            self.parent.set(i, r);
            proof {
                s0.lemma_root(p);
                assert forall|j: usize| 0 <= j < self.parent.len() implies
                    #[trigger] self.spec_find(j) == s0.spec_find(j) by {
                    s0.lemma_upd(self, i, j);
                }
                assert forall|k: usize| 0 <= k < self.parent.len() implies {
                    let q = #[trigger] self.parent[k as int];
                    &&& q < self.parent.len()
                    &&& self.rank[k as int] < self.parent.len()
                    &&& (q != k ==> self.rank[k as int] < self.rank[q as int])
                } by {
                    if k == i {
                        s0.lemma_root(i);
                    } else {
                        assert(s1.parent[k as int] == self.parent[k as int]);
                    }
                }
            }
            r
        }
'''
s=s.replace("// <helpers>\n","// <helpers>\n"+h,1)
s=s.replace("        {\n            // TODO: Implement the find operation with path compression for union-find data structure here.\n        }","        {\n            self.find_rec(i)\n        }")
open('unionfind_find.rs','w').write(s)
