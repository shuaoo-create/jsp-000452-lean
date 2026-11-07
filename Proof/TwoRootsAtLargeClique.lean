import UnpaidRequiresBigClique
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

theorem cold_vertex_root_degree (Q : SimpleGraph X) (I : Set X) (D : ℕ)
    (four : 4≤D) (reg : ∀v,Nat.card (Q.neighborSet v)=D) (s : HeavyCliqueFrame Q I D)
    (z : X) (zc : z∈s.cliquePart) (cold : ¬Q.Adj s.pivot z) :
    (Q.neighborSet z∩I).ncard=2 := by
  let N := Q.neighborSet z
  let C := s.cliquePart
  have internal : N∩C=C\{z} := by
    ext w
    exact ⟨fun h => ⟨h.2,fun eq => (show Q.Adj z w from h.1).ne (Set.mem_singleton_iff.mp eq).symm⟩,
      fun h => ⟨s.clique zc h.1 (fun eq => h.2 (Set.mem_singleton_iff.mpr eq.symm)),h.1⟩⟩
  have split : (N∩I)∪(N∩C)=N := by
    ext w
    constructor
    · exact fun h => h.elim (fun a => a.1) (fun a => a.1)
    · intro edge
      by_cases wc:w∈C
      · exact Or.inr ⟨edge,wc⟩
      rcases s.cliqueEdges z zc w edge wc with wi|wa
      · exact Or.inl ⟨edge,wi⟩
      · exact (cold (wa ▸ (show Q.Adj z w from edge).symm)).elim
  have dis : Disjoint (N∩I) (N∩C) := Set.disjoint_left.mpr (fun _ h k => s.cOut k.2 h.2)
  have sum := congrArg Set.ncard split
  rw [Set.ncard_union_eq dis,internal,←Nat.card_coe_set_eq N,reg] at sum
  have rem := Set.ncard_sdiff_singleton_add_one (show z∈C from zc)
  have size : C.ncard=D-1 := s.order
  change (N∩I).ncard=2
  omega

theorem two_cold_clique_vertices (Q : SimpleGraph X) (I : Set X) (D : ℕ)
    (four : 4≤D) (reg : ∀v,Nat.card (Q.neighborSet v)=D) (s : HeavyCliqueFrame Q I D)
    (r:X) (ri:r∈I) (ar:Q.Adj s.pivot r) :
    ∃z∈s.cliquePart,∃w∈s.cliquePart,z≠w ∧ ¬Q.Adj s.pivot z ∧ ¬Q.Adj s.pivot w := by
  obtain ⟨u,us,v,vs,uv,au,av⟩ := s.two
  let N := Q.neighborSet s.pivot
  let B := N∩s.cliquePart
  have sub : B∪{u,v,r} ⊆ N := by
    rintro _ (h|e|e|e)
    · exact h.1
    · exact e.symm ▸ au
    · exact e.symm ▸ av
    · exact (Set.mem_singleton_iff.mp e).symm ▸ ar
  have dis : Disjoint B ({u,v,r}:Set X) := by
    apply Set.disjoint_left.mpr
    rintro t h (e|e|e)
    · exact Set.disjoint_left.mp s.dis us (e ▸ h.2)
    · exact Set.disjoint_left.mp s.dis vs (e ▸ h.2)
    · exact s.cOut h.2 ((Set.mem_singleton_iff.mp e).symm ▸ ri)
  have ur : u≠r := fun e => s.sOut us (e.symm ▸ ri)
  have vr : v≠r := fun e => s.sOut vs (e.symm ▸ ri)
  have bound := Set.ncard_le_ncard sub
  rw [Set.ncard_union_eq dis,Set.ncard_insert_of_notMem (by simp [uv,ur]),Set.ncard_pair vr,
    ←Nat.card_coe_set_eq N,reg] at bound
  have split := Set.ncard_sdiff_add_ncard_of_subset (show B⊆s.cliquePart from Set.inter_subset_right)
  have size := s.order
  obtain ⟨z,w,hz,hw,ne⟩ := (Set.one_lt_ncard_iff (Set.toFinite (s.cliquePart\B))).mp (by omega)
  exact ⟨z,hz.1,w,hw.1,ne,fun e => hz.2 ⟨e,hz.1⟩,fun e => hw.2 ⟨e,hw.1⟩⟩

/-- Two clique vertices outside the pivot neighbourhood force all the
clique-to-root edges onto at most two roots by the independent-cut rank. -/
theorem only_two_roots_touch_clique [Nonempty X] (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A:Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (four : 4≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q) (zero : baseReserve Q D=0) (s : HeavyCliqueFrame Q I D) :
    ∃r∈I,∃t∈I,r≠t ∧ Q.Adj s.pivot r ∧ ∃z∈s.cliquePart,
      Q.Adj z r ∧ Q.Adj z t ∧ ∀c∈s.cliquePart,∀i∈I,Q.Adj c i → i=r ∨ i=t := by
  classical
  obtain ⟨r,ri,ar⟩ := largest_independent_dominates Q I ind largest s.pivot s.ai
  obtain ⟨z,zc,w,wc,zw,az,aw⟩ := two_cold_clique_vertices Q I D four reg s r ri ar
  have dz := cold_vertex_root_degree Q I D four reg s z zc az
  have dw := cold_vertex_root_degree Q I D four reg s w wc aw
  obtain ⟨t,⟨zt,ti⟩,tr'⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show ({r}:Set X).ncard<(Q.neighborSet z∩I).ncard by rw [Set.ncard_singleton,dz];omega)
  have tr : t≠r := by simpa using tr'
  have block := no_two_clique_root_edges Q I D four par reg crit zero s r ri ar
  have wsub : Q.neighborSet w∩I⊆{r,t} := by
    intro i h
    by_cases ir:i=r
    · exact Or.inl ir
    · exact Or.inr (Set.mem_singleton_iff.mpr (by
        by_contra it
        exact block w z i t wc zc zw.symm h.2 ti ir tr it h.1 zt))
  have weq : Q.neighborSet w∩I={r,t} := by
    apply Set.eq_of_subset_of_ncard_le wsub
    rw [dw,Set.ncard_pair tr.symm]
  have wt : Q.Adj w t :=
    (show t∈Q.neighborSet w∩I from weq.symm ▸ (show t∈({r,t}:Set X) by simp)).1
  have keep (c:X) (cc:c∈s.cliquePart) (i:X) (ii:i∈I) (edge:Q.Adj c i) : i=r ∨ i=t := by
    by_cases ir:i=r
    · exact Or.inl ir
    right
    by_contra it
    by_cases same:c=z
    · exact block c w i t cc wc (same.symm ▸ zw) ii ti ir tr it edge wt
    · exact block c z i t cc zc same ii ti ir tr it edge zt
  have zsub : Q.neighborSet z∩I⊆{r,t} := by
    intro i h
    rcases keep z zc i h.2 h.1 with hr|ht
    · exact Or.inl hr
    · exact Or.inr (Set.mem_singleton_iff.mpr ht)
  have zeq : Q.neighborSet z∩I={r,t} := by
    apply Set.eq_of_subset_of_ncard_le zsub
    rw [dz,Set.ncard_pair tr.symm]
  have zr : Q.Adj z r :=
    (show r∈Q.neighborSet z∩I from zeq.symm ▸ (show r∈({r,t}:Set X) by simp)).1
  exact ⟨r,ri,t,ti,tr.symm,ar,z,zc,zr,zt,keep⟩

#print axioms only_two_roots_touch_clique
end JSP452Audit.StarHost
