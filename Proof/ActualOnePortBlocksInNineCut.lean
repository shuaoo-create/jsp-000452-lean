import MaximalNineCutOnActualVertexSets
namespace JSP452Audit.StarHost.NineOriginalCut
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:NineOriginalCut G)

abbrev labels (c:↥K.blocks) := cutPieceSet G K.barrier c.val
noncomputable abbrev sPorts (c:↥K.blocks) := crossCount G (K.labels c) K.S
noncomputable abbrev tPorts (c:↥K.blocks) := crossCount G (K.labels c) K.T
def onePortBlocks : Set ↥K.blocks := {c | K.sPorts c=1 ∧ K.tPorts c=0}

theorem region_root_budgets (cap:∀x,Nat.card (G.neighborSet x)≤9) :
    crossCount G K.region K.S+crossCount G K.T K.S≤9*K.S.ncard ∧
    crossCount G K.region K.T+crossCount G K.T K.S≤9*K.T.ncard := by
  have out : K.region⊆K.barrierᶜ := by rintro _ ⟨v,rfl,_⟩;exact v.property
  have js : Disjoint K.S K.region := disjoint_compl_right.mono Set.subset_union_left out
  have jt : Disjoint K.T K.region := disjoint_compl_right.mono Set.subset_union_right out
  have left := cross_from_root_bound G 9 cap K.S (K.T∪K.region) (Set.disjoint_union_right.mpr ⟨K.apart,js⟩)
  have right := cross_from_root_bound G 9 cap K.T (K.S∪K.region) (Set.disjoint_union_right.mpr ⟨K.apart.symm,jt⟩)
  rw [cut_cross_union_right G K.S K.T K.region jt,crossCount_swap G K.S K.T,crossCount_swap G K.S K.region] at left
  rw [cut_cross_union_right G K.T K.S K.region js,crossCount_swap G K.T K.region] at right
  omega

theorem one_port_lower_bound (cap:∀x,Nat.card (G.neighborSet x)≤9) :
    3*K.eta≤2*(K.onePortBlocks.ncard:ℤ) := by
  classical
  let _ := Fintype.ofFinite ↥K.blocks
  have localFee (c:↥K.blocks) : 3≤K.sPorts c+2*K.tPorts c+(if c∈K.onePortBlocks then 2 else 0) := by
    have parity := counted_piece_has_odd_source_ports G 3 6 (by decide) (by decide) cap K.S K.T K.apart c.val c.property
    change Odd (K.sPorts c) at parity
    obtain ⟨m,eq⟩ := parity
    by_cases one:c∈K.onePortBlocks
    · rw [if_pos one];omega
    · rw [if_neg one]
      change ¬(K.sPorts c=1 ∧ K.tPorts c=0) at one
      omega
  have total := Finset.sum_le_sum (s:=(Finset.univ:Finset ↥K.blocks)) (fun c _ => localFee c)
  have indicator : (∑c:↥K.blocks,if c∈K.onePortBlocks then 2 else 0)=2*K.onePortBlocks.ncard := by
    calc
      _ = ∑c∈(Finset.univ.filter (fun c:↥K.blocks => c∈K.onePortBlocks)),2 := (Finset.sum_filter _ _).symm
      _ = _ := by simp [Set.ncard_eq_toFinset_card',Nat.mul_comm]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,indicator,
    Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id] at total
  have s := selected_cut_cross_sum G K.barrier K.blocks K.S
  have t := selected_cut_cross_sum G K.barrier K.blocks K.T
  change crossCount G K.region K.S=∑c:↥K.blocks,K.sPorts c at s
  change crossCount G K.region K.T=∑c:↥K.blocks,K.tPorts c at t
  change K.blocks.ncard*3≤(∑c:↥K.blocks,K.sPorts c)+2*(∑c:↥K.blocks,K.tPorts c)+2*K.onePortBlocks.ncard at total
  rw [←s,←t] at total
  obtain ⟨left,right⟩ := K.region_root_budgets cap
  have eq := uniform_factor_cut_on_original G 3 6 K.S K.T
  change K.eta=(K.blocks.ncard:ℤ)+(crossCount G K.T K.S:ℤ)-3*(K.S.ncard:ℤ)-6*(K.T.ncard:ℤ) at eq
  omega

#print axioms region_root_budgets
#print axioms one_port_lower_bound
end JSP452Audit.StarHost.NineOriginalCut
