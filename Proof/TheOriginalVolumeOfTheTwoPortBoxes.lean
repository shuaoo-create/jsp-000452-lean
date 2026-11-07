import TwoLeafCostsInBothActualResidualLists
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem nine_removal_volume_guard {s : ℕ} {X : Type*} [Finite X] {G : SimpleGraph X} (K : NinePortRegion G)
    (n : Fin s→ℕ) (pn : ∀i,1≤n i) :
    let H := G.induce K.chosen
    let μ := matchingEdges H
    let W := componentBudget H n
    let u := s-originalThresholdCount n 2
    μ≤u+2+3*(μ-W.loss) := by
  classical
  intro H μ W u
  obtain ⟨T,mem,size⟩ := Finset.exists_mem_eq_sup W.choices W.present Finset.card
  change W.loss=T.card at size
  obtain ⟨bound,slots⟩ := (mem_component_budget H n T).mp mem
  obtain ⟨f,_⟩ := slots
  have place := Nat.card_le_card_of_injective f f.injective
  change Nat.card (Σz:↥T,Fin (n z.val+1))≤Nat.card ↥K.chosen at place
  rw [Nat.card_sigma] at place
  simp only [Nat.card_fin,Nat.card_coe_set_eq] at place
  have per (z:↥T) : 3≤n z.val+1+(if n z.val<2 then 1 else 0) := by have := pn z.val;split_ifs <;> omega
  have whole := Finset.sum_le_sum (s:=Finset.univ) (fun z _ => per z)
  let S := Finset.univ.filter (fun z:↥T => n z.val<2)
  let V := Finset.univ.filter (fun z:Fin s => n z<2)
  let send : ↥S → ↥V := fun z => ⟨z.val.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp z.property).2⟩⟩
  have inj : Function.Injective send := fun _ _ eq => Subtype.ext (Subtype.ext (congrArg (fun z:↥V => z.val) eq))
  have fewer : S.card≤V.card := by simpa using Fintype.card_le_of_injective send inj
  have orig : V.card=u := units_outside_high_prefix n
  have all : T.card*3≤(∑z:↥T,(n z.val+1))+S.card := by
    simpa [S,Finset.sum_add_distrib,Finset.sum_boole] using whole
  have ord := K.chosen_structure.1
  have capRank : matchingEdges (G.induce K.chosen)=K.totalCapacity := by
    obtain ⟨iso⟩ := K.chosen_structure.2
    have hp := rank_eq_of_graph_iso iso
    rw [matchingEdges_sumGraph] at hp
    exact hp.symm
  change matchingEdges H=K.totalCapacity at capRank
  change K.chosen.ncard=2*K.totalCapacity+2 at ord
  change μ=K.totalCapacity at capRank
  change T.card≤μ at bound
  omega

theorem strict_nine_doubled_unit_volume (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) (long : R.totalCapacity<F.s)
    (few : originalThresholdCount F.n 2≤R.totalCapacity) :
    let P := R.totalCapacity
    let W := componentBudget (F.G.induce R.chosen) F.n
    let delta := P-W.loss
    let d := F.rank-matchingEdges F.G-R.rankAllowance
    let Y := ∑j,(F.m j-1)/2
    let u := F.s-originalThresholdCount F.n 2
    P+F.r+2*d+2*Y≤2*u+2*delta+1 := by
  intro P W delta d Y u
  have cap (v) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq nine
  have vol := nine_removal_volume_guard R F.n F.pn
  change matchingEdges (F.G.induce R.chosen)≤u+2+3*(matchingEdges (F.G.induce R.chosen)-W.loss) at vol
  rw [(R.region_rank_edges cap).1] at vol
  change P≤u+2+3*delta at vol
  have root := R.root_count.1
  change 1≤R.roots.ncard at root
  have guard := (nine_long_side_exterior_endpoints F paid nine R long).1
  change R.roots.ncard+F.r+2*(d+Y)+delta≤F.s-P at guard
  change originalThresholdCount F.n 2≤P at few
  change P<F.s at long
  dsimp only [u] at vol ⊢;omega

#print axioms nine_removal_volume_guard
#print axioms strict_nine_doubled_unit_volume
end JSP452Audit.StarHost
