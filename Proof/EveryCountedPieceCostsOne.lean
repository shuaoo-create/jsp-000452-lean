import SumTheActualOptimalMatchingCharges
namespace JSP452Audit.StarHost.NineOriginalCut
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:NineOriginalCut G)

theorem matching_use_equals_one (cap:∀x,Nat.card (G.neighborSet x)≤9) (few:minimumExposure G 9≤4)
    (gap:K.S.ncard=K.T.ncard+1) (pos:1≤K.eta) (M:G.Subgraph) (hm:M.IsMatching)
    (optimal:(exposedFull G M 9).ncard=minimumExposure G 9) (c:↥K.blocks) : K.matchingUse M c=1 := by
  classical
  let _ := Fintype.ofFinite ↥K.blocks
  have allPositive (d:↥K.blocks) : 1≤K.matchingUse M d := by obtain ⟨k,eq⟩ := (K.matching_use_local cap M hm d).1;omega
  have sum := K.matching_use_global cap M hm optimal
  have other := Finset.sum_le_sum (s:=Finset.univ.erase c) (fun i _ => allPositive i)
  rw [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ c),Finset.card_univ,←Nat.card_eq_fintype_card,
    nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at other
  change K.blocks.ncard-1≤∑i∈Finset.univ.erase c,K.matchingUse M i at other
  have total := Finset.add_sum_erase (s:=Finset.univ) (K.matchingUse M) (Finset.mem_univ c)
  have eq := uniform_factor_cut_on_original G 3 6 K.S K.T
  change K.eta=(K.blocks.ncard:ℤ)+(crossCount G K.T K.S:ℤ)-3*(K.S.ncard:ℤ)-6*(K.T.ncard:ℤ) at eq
  obtain ⟨n,odd⟩ := (K.matching_use_local cap M hm c).1
  omega

#print axioms matching_use_equals_one
end JSP452Audit.StarHost.NineOriginalCut
