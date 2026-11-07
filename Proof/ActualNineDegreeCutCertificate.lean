import OddHostCutNeedsSourcePort
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

structure NineOriginalCut {X:Type u} (G:SimpleGraph X) where
  S : Set X
  T : Set X
  apart : Disjoint S T

namespace NineOriginalCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:NineOriginalCut G)
noncomputable abbrev eta := originalFactorCut G 3 6 K.S K.T
abbrev barrier := K.S∪K.T
noncomputable abbrev blocks := uniformOddPieces G 3 6 K.S K.T
noncomputable abbrev region := regionCore G K.barrier K.blocks

theorem left_port_budget (cap:∀x,Nat.card (G.neighborSet x)≤9) :
    K.blocks.ncard+crossCount G K.T K.S≤9*K.S.ncard := by
  classical
  let _ := Fintype.ofFinite ↥K.blocks
  have one (c:↥K.blocks) : 1≤crossCount G (cutPieceSet G K.barrier c.val) K.S := by
    have parity := counted_piece_has_odd_source_ports G 3 6 (by decide) (by decide) cap K.S K.T K.apart c.val c.property
    change Odd (crossCount G (cutPieceSet G K.barrier c.val) K.S) at parity
    obtain ⟨n,eq⟩ := parity;omega
  have sum := Finset.sum_le_sum (s:=(Finset.univ:Finset ↥K.blocks)) (fun c _ => one c)
  rw [←selected_cut_cross_sum,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at sum
  change K.blocks.ncard≤crossCount G K.region K.S at sum
  have out : K.region⊆K.barrierᶜ := by rintro _ ⟨v,rfl,_⟩;exact v.property
  have apart : Disjoint K.T K.region := disjoint_compl_right.mono Set.subset_union_right out
  have all := cross_from_root_bound G 9 cap K.S (K.T∪K.region)
    (Set.disjoint_union_right.mpr ⟨K.apart,disjoint_compl_right.mono Set.subset_union_left out⟩)
  rw [cut_cross_union_right G K.S K.T K.region apart,crossCount_swap G K.S K.T,crossCount_swap G K.S K.region] at all
  omega

theorem endpoint_on_same_cut (cap:∀x,Nat.card (G.neighborSet x)≤9) :
    K.eta+2*(K.S.ncard:ℤ)-2*(K.T.ncard:ℤ)≤(minimumExposure G 9:ℤ) := by
  have price := matching_endpoint_cut G 9 (by decide) cap K.S K.T K.apart
  rw [uniform_factor_cut_on_original] at price
  have eq := same_odd_capacity_piece_family G 3 6 1 8 (by decide) (by decide) (by decide) K.S K.T
  change ((uniformOddPieces G 1 8 K.S K.T).ncard:ℤ)+(crossCount G K.T K.S:ℤ)-1*(K.S.ncard:ℤ)-8*(K.T.ncard:ℤ)≤_ at price
  rw [←eq] at price
  have old := uniform_factor_cut_on_original G 3 6 K.S K.T
  change K.eta=(K.blocks.ncard:ℤ)+(crossCount G K.T K.S:ℤ)-3*(K.S.ncard:ℤ)-6*(K.T.ncard:ℤ) at old
  change (K.blocks.ncard:ℤ)+(crossCount G K.T K.S:ℤ)-1*(K.S.ncard:ℤ)-8*(K.T.ncard:ℤ)≤_ at price
  omega

theorem actual_root_gap (cap:∀x,Nat.card (G.neighborSet x)≤9) (few:minimumExposure G 9≤4)
    (positive:1≤K.eta) : K.S.ncard=K.T.ncard+1 ∧ K.eta+2≤(minimumExposure G 9:ℤ) := by
  have left := K.left_port_budget cap
  have right := K.endpoint_on_same_cut cap
  have eq := uniform_factor_cut_on_original G 3 6 K.S K.T
  change K.eta=(K.blocks.ncard:ℤ)+(crossCount G K.T K.S:ℤ)-3*(K.S.ncard:ℤ)-6*(K.T.ncard:ℤ) at eq
  omega

#print axioms left_port_budget
#print axioms endpoint_on_same_cut
#print axioms actual_root_gap
end NineOriginalCut
end JSP452Audit.StarHost
