import ActualOnePortBlocksInNineCut
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem cross_count_mono {X:Type*} [Finite X] (G:SimpleGraph X) {U V U' V':Set X} (s:U⊆U') (t:V⊆V') :
    crossCount G U V≤crossCount G U' V' := by
  let f (x:{z:↥U×↥V // G.Adj z.1.val z.2.val}) : {z:↥U'×↥V' // G.Adj z.1.val z.2.val} :=
    ⟨(⟨x.val.1.val,s x.val.1.property⟩,⟨x.val.2.val,t x.val.2.property⟩),x.property⟩
  apply Nat.card_le_card_of_injective f
  intro x y eq
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun w:{z:↥U'×↥V' // G.Adj z.1.val z.2.val} => w.val.1.val) eq)
  · exact Subtype.ext (congrArg (fun w:{z:↥U'×↥V' // G.Adj z.1.val z.2.val} => w.val.2.val) eq)

theorem root_shortfall_sum {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ) (A:Set X)
    (cap:∀x∈A,Nat.card (G.neighborSet x)≤D) :
    rootShortfall G A D=∑x∈A.toFinite.toFinset,(D-Nat.card (G.neighborSet x)) := by
  classical
  have eq := Finset.sum_congr (s₁:=A.toFinite.toFinset) rfl (fun x hx =>
    Nat.sub_add_cancel (cap x (A.toFinite.mem_toFinset.mp hx)))
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at eq
  have card : A.toFinite.toFinset.card=A.ncard := by rw [←Set.ncard_coe_finset,A.toFinite.coe_toFinset]
  rw [card,Nat.mul_comm A.ncard D] at eq
  change (∑x∈A.toFinite.toFinset,(D-Nat.card (G.neighborSet x)))+originalDegreeSum G A=D*A.ncard at eq
  unfold rootShortfall;omega

theorem root_shortfall_mono {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ) {A S:Set X} (sub:A⊆S)
    (cap:∀x,Nat.card (G.neighborSet x)≤D) : rootShortfall G A D≤rootShortfall G S D := by
  rw [root_shortfall_sum G D A (fun x _ => cap x),root_shortfall_sum G D S (fun x _ => cap x)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => S.toFinite.mem_toFinset.mpr (sub (A.toFinite.mem_toFinset.mp hx))) (fun _ _ _ => Nat.zero_le _)

namespace NineOriginalCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:NineOriginalCut G)

theorem root_debt_with_internal_edges (cap:∀x,Nat.card (G.neighborSet x)≤9)
    (gap:K.S.ncard=K.T.ncard+1) (A:Set X) (sub:A⊆K.S) :
    (rootShortfall G A 9:ℤ)+2*((G.induce A).edgeSet.ncard:ℤ)+K.eta≤6 := by
  classical
  let _ := Fintype.ofFinite ↥K.blocks
  let O := K.barrierᶜ
  have out : K.region⊆O := by rintro _ ⟨x,rfl,_⟩;exact x.property
  have odd (c:↥K.blocks) : 1≤K.sPorts c := by
    have parity := counted_piece_has_odd_source_ports G 3 6 (by decide) (by decide) cap K.S K.T K.apart c.val c.property
    change Odd (K.sPorts c) at parity;obtain ⟨v,eq⟩ := parity;omega
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun c _ => odd c)
  rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at total
  have sum := selected_cut_cross_sum G K.barrier K.blocks K.S
  change crossCount G K.region K.S=∑c:↥K.blocks,K.sPorts c at sum
  rw [←sum,crossCount_swap G K.region K.S] at total
  have mon := cross_count_mono G (Set.Subset.rfl (s:=K.S)) out
  have so : Disjoint K.S O := disjoint_compl_right.mono_left Set.subset_union_left
  have to' : Disjoint K.T O := disjoint_compl_right.mono_left Set.subset_union_right
  have hand := partition_handshake G K.S K.T O K.apart so to' (Set.union_compl_self _)
  rw [crossCount_swap G K.S K.T] at hand
  have paid := degree_sum_le_cap G K.S 9 (fun x _ => cap x)
  have debt := root_shortfall_mono G 9 sub cap
  change rootShortfall G A 9≤9*K.S.ncard-originalDegreeSum G K.S at debt
  have edges := cross_count_mono G sub sub
  rw [crossCount_self,crossCount_self] at edges
  have eq := uniform_factor_cut_on_original G 3 6 K.S K.T
  change K.eta=(K.blocks.ncard:ℤ)+(crossCount G K.T K.S:ℤ)-3*(K.S.ncard:ℤ)-6*(K.T.ncard:ℤ) at eq
  change K.blocks.ncard≤crossCount G K.S K.region at total
  omega

#print axioms root_debt_with_internal_edges
end NineOriginalCut
#print axioms cross_count_mono
#print axioms root_shortfall_sum
#print axioms root_shortfall_mono
end JSP452Audit.StarHost
