import OnePreferredPart
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

/-- In a zero-reserve graph each exposed root has a partner root that,
together with it, covers every exposable point of the single preferred part. -/
theorem single_part_exposable_cover (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (D : ℕ) (pos : 1≤D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q) (zero : baseReserve Q D=0) (s : OnePreferredPart Q I)
    (i : X) (hi : i∈I) :
    ∃u∈I,u≠i ∧ ∀v:s.preferred,ExposablePoint (Q.induce s.preferred) v →
      Q.Adj i v.val ∨ Q.Adj u v.val := by
  classical
  obtain ⟨A,perf⟩ := crit i
  obtain ⟨M,hm,supp,_⟩ := lift_perfect_off_vertex_maximum Q i A perf
  let W := independentMateLabels Q I i M
  have usedNe {a b} (edge:M.Adj a b) : a≠i := by
    have h := M.edge_vert edge
    rwa [supp] at h
  have sub : s.singles⊆W := by
    intro v hv
    have active : v∈M.verts := by rw [supp];exact fun eq => s.sOut hv (eq.symm ▸ hi)
    obtain ⟨u,edge,_⟩ := hm active
    exact ⟨s.sOut hv,u,s.isolated v hv u (M.adj_sub edge),usedNe edge.symm,edge.symm⟩
  have wc : W.ncard+1=I.ncard := independentMateLabels_card Q I ind i hi M hm supp
  have cnt := s.count
  obtain ⟨p,pW,ps⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show s.singles.ncard<W.ncard by omega)
  have pp : p∈s.preferred := (s.cover p).elim (fun h => (pW.1 h).elim)
    (fun h => h.resolve_left ps)
  obtain ⟨_,u,hu,ui,up⟩ := pW
  have exactW : insert p s.singles=W := by
    apply Set.eq_of_subset_of_ncard_le
    · exact Set.insert_subset (show p∈W from ⟨s.pOut pp,u,hu,ui,up⟩) sub
    · rw [Set.ncard_insert_of_notMem ps];omega
    · exact Set.toFinite W
  refine ⟨u,hu,ui,?_⟩
  intro v ex
  apply roots_cover_exposable_points Q D pos reg crit zero M hm i u ui
    (fun edge => ind hi hu ui.symm edge) s.preferred (fun h => s.pOut h hi)
    (fun h => s.pOut h hu) supp p pp up _ v ex
  intro a ha b edge out
  have bi := s.external a ha b (M.adj_sub edge) out
  have aW : a∈W := ⟨s.pOut ha,b,bi,usedNe edge.symm,edge.symm⟩
  rw [←exactW] at aW
  rcases aW with same|hs
  · subst a;exact hm.eq_of_adj_left edge up.symm
  · exact (Set.disjoint_left.mp s.dis hs ha).elim

omit [Nonempty X] in
theorem single_part_root_degree (Q : SimpleGraph X) (I : Set X) (D : ℕ)
    (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (s : OnePreferredPart Q I) (many : 3≤I.ncard) : D≤I.ncard := by
  have count := s.count
  obtain ⟨a,ha⟩ := (Set.ncard_pos (Set.toFinite s.singles)).mp (show 0<s.singles.ncard by omega)
  have sub : Q.neighborSet a⊆I := s.isolated a ha
  have bound := Set.ncard_le_ncard sub
  rw [←Nat.card_coe_set_eq (Q.neighborSet a),reg] at bound
  exact bound

omit [Nonempty X] in
private theorem critical_internal_degree_ge_two (G : SimpleGraph X) (crit : PerfectAfterEveryDeletion G)
    (three : 3≤Nat.card X) (v : X) : 2≤Nat.card (G.neighborSet v) := by
  classical
  by_contra! few
  have cap : (G.neighborSet v).ncard≤1 := by rw [←Nat.card_coe_set_eq];omega
  obtain ⟨w,vw⟩ : ∃w:X,v≠w := by
    obtain ⟨w,_,diff⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
      (show ({v} : Set X).ncard<(Set.univ : Set X).ncard by rw [Set.ncard_singleton,Set.ncard_univ];omega)
    exact ⟨w,fun eq => diff (Set.mem_singleton_iff.mpr eq.symm)⟩
  obtain ⟨M,pm⟩ := crit w
  let v' : {x : X|x≠w} := ⟨v,vw⟩
  obtain ⟨a,adj,_⟩ := Subgraph.isPerfectMatching_iff.mp pm v'
  have va : G.Adj v a.val := M.adj_sub adj
  obtain ⟨N,pn⟩ := crit a.val
  let u : {x : X | x≠a.val} := ⟨v,va.ne⟩
  obtain ⟨b,edge,_⟩ := Subgraph.isPerfectMatching_iff.mp pn u
  have vb : G.Adj v b.val := N.adj_sub edge
  exact b.property ((Set.ncard_le_one (Set.toFinite _)).mp cap b.val vb a.val va)

/-- A fully exposable single preferred part larger than D cannot belong to
a zero-reserve factor-critical host. -/
theorem large_critical_single_part_pays (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard) (many : 3≤I.ncard)
    (D : ℕ) (six : 6≤D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q) (s : OnePreferredPart Q I)
    (large : D+1≤s.preferred.ncard) (pcrit : PerfectAfterEveryDeletion (Q.induce s.preferred)) :
    1≤baseReserve Q D := by
  classical
  let P := s.preferred
  let _ := Fintype.ofFinite P
  change D+1≤P.ncard at large
  let f (v:P) := (Q.neighborSet v.val∩I).ncard
  have sum : ∑v,f v=2*D := by
    have cost := (one_preferred_exact_boundary Q I ind D reg s).2
    rw [crossCount_swap,crossCount_eq_neighbor_sum] at cost
    exact cost
  have unit : ∃v:P,f v=1 := by
    by_contra! all
    have low (v:P) : 2≤f v := by
      obtain ⟨r,ri,edge⟩ := largest_independent_dominates Q I ind largest v.val (s.pOut v.property)
      have positive := (Set.ncard_pos (Set.toFinite (Q.neighborSet v.val∩I))).mpr ⟨r,edge,ri⟩
      have ne := all v
      change 0<f v at positive;omega
    have bound := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => low v)
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ] at bound
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,sum] at bound
    change P.ncard*2≤2*D at bound
    omega
  obtain ⟨v,unitV⟩ := unit
  obtain ⟨r,vr,ri⟩ := (Set.ncard_pos (Set.toFinite (Q.neighborSet v.val∩I))).mp (show 0<f v by omega)
  have unique (j:X) (ji:j∈I) (adj : Q.Adj v.val j) : j=r :=
    (Set.ncard_le_one (Set.toFinite _)).mp unitV.le j ⟨adj,ji⟩ r ⟨vr,ri⟩
  have rcard : (Q.neighborSet r).ncard=D := (Nat.card_coe_set_eq _).symm.trans (reg r)
  obtain ⟨w,wp,miss⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show (Q.neighborSet r).ncard<P.ncard by rw [rcard];omega)
  by_contra! fail
  have zero : baseReserve Q D=0 := by omega
  have all (i:X) (hi:i∈I) (ne:i≠r) : Q.Adj i w := by
    obtain ⟨u,hu,_,cover⟩ := single_part_exposable_cover Q I ind D (by omega) reg crit zero s i hi
    have ur : u=r := by
      rcases cover v (pcrit v) with first|second
      · exact (ne (unique i hi first.symm)).elim
      · exact unique u hu second.symm
    rcases cover ⟨w,wp⟩ (pcrit ⟨w,wp⟩) with edge|edge
    · exact edge
    · exact (miss (ur ▸ edge)).elim
  have sub : I\{r} ⊆ Q.neighborSet w∩Pᶜ := by
    intro i hi
    exact ⟨(all i hi.1 (by simpa using hi.2)).symm,fun hp => s.pOut hp hi.1⟩
  have lower := Set.ncard_le_ncard sub
  have lose := Set.ncard_sdiff_singleton_add_one ri
  have countI := single_part_root_degree Q I D reg s many
  have inn := critical_internal_degree_ge_two (Q.induce P) pcrit
    (by rw [Nat.card_coe_set_eq];exact s.big) ⟨w,wp⟩
  rw [induced_degree_intersection] at inn
  let N := Q.neighborSet w
  have split : (N∩P)∪(N∩Pᶜ)=N := by rw [←Set.inter_union_distrib_left,Set.union_compl_self,Set.inter_univ]
  have dis : Disjoint (N∩P) (N∩Pᶜ) := disjoint_compl_right.mono Set.inter_subset_right Set.inter_subset_right
  have sumN := congrArg Set.ncard split
  rw [Set.ncard_union_eq dis,←Nat.card_coe_set_eq N,reg] at sumN
  change 2≤(N∩P).ncard at inn
  change (I\{r}).ncard≤(N∩Pᶜ).ncard at lower
  omega

#print axioms single_part_exposable_cover
#print axioms large_critical_single_part_pays
end JSP452Audit.StarHost
