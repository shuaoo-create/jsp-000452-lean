import LargeCriticalPreferred
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

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
theorem large_critical_single_part_pays_from_four (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard) (many : 3≤I.ncard)
    (D : ℕ) (four : 4≤D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
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

#print axioms large_critical_single_part_pays_from_four
end JSP452Audit.StarHost
