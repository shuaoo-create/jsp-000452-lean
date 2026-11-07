import OriginalEightDegreeInventory
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem matching_endpoint_cut {X:Type u} [Finite X] (G:SimpleGraph X) (D:ℕ) (pos:0<D)
    (cap:∀v,Nat.card (G.neighborSet v)≤D) (S T:Set X) (dis:Disjoint S T) :
    originalFactorCut G 1 (D-1) S T≤(minimumExposure G D:ℤ) := by
  classical
  let _ := Fintype.ofFinite X
  let P : JSP452Audit.Padded.Spec X := ⟨G,fun _ => 1,fun _ => D-1,false⟩
  have eqdeg (x:X) : G.degree x=Nat.card (G.neighborSet x) := by
    rw [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree]
  have caps (x:X) : P.G.degree x≤P.A x+P.B x := by
    change G.degree x≤1+(D-1);rw [eqdeg];have := cap x;omega
  have signed := P.cutDeficit_le_minColorGap dis caps
  obtain ⟨M,matchM,_,optimal⟩ := minimumExposure_attained G D
  let R := M.spanningCoe
  let W := exposedFull G M D
  have term (x:X) : (Nat.card (R.neighborSet x)-1)+(G.degree x-Nat.card (R.neighborSet x)-(D-1))=
      if x∈W then 1 else 0 := by
    have one := spanningMatching_degree_le_one M matchM x
    change Nat.card (R.neighborSet x)≤1 at one
    rw [eqdeg]
    have d := cap x
    by_cases hit:x∈M.verts
    · obtain ⟨y,e,_⟩ := matchM hit
      have positive : 0<(R.neighborSet x).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨y,e⟩
      have used : 0<Nat.card (R.neighborSet x) := positive
      rw [if_neg (fun h => (show x∈exposedFull G M D from h).1 hit)];omega
    · have none : R.neighborSet x=∅ := Set.eq_empty_of_forall_notMem (fun y h => hit (M.edge_vert h))
      rw [none,Nat.card_coe_set_eq,Set.ncard_empty]
      by_cases full:Nat.card (G.neighborSet x)=D
      · rw [if_pos (show x∈W from ⟨hit,full⟩)];omega
      · rw [if_neg (fun h => full (show x∈exposedFull G M D from h).2)];omega
  have color : P.colorGap R=W.ncard := by
    change (∑x:X,((Nat.card (R.neighborSet x)-1)+(G.degree x-Nat.card (R.neighborSet x)-(D-1))))=W.ncard
    simp_rw [term]
    rw [←Finset.sum_filter]
    simp [Set.ncard_eq_toFinset_card']
  have test : P.minColorGap≤P.colorGap R :=
    Nat.sInf_le (show P.colorGap R∈{n:ℕ|∃F:SimpleGraph X,F≤P.G ∧ P.colorGap F=n} from ⟨R,M.spanningCoe_le,rfl⟩)
  change W.ncard=minimumExposure G D at optimal
  change P.cutDeficit S T≤_
  omega

#print axioms matching_endpoint_cut
end JSP452Audit.StarHost
