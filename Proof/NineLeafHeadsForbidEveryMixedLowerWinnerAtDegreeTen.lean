import TwoSlotPricesLimitTheRegularCapacityAtDegreeTen
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem PricedTenMenu.outlast (F:StrictFamily.{u}) (A:PricedTenMenu F) [DecidableEq ↥A.K.selected] (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (k:ℕ) (menu:SplitCapacities A.units (F.r+k))
    (B:Set ↥(A.K.supportᶜ:Set F.X)) (first:CompleteDegreeStage (F.G.induce A.K.supportᶜ) 10 B)
    (C:Set ↥(Bᶜ:Set _)) (second:CompleteDegreeStage ((F.G.induce A.K.supportᶜ).induce Bᶜ) 9 C) :
    B.ncard+C.ncard<k := by
  classical
  let e : ↥A.K.selected ↪ F.G.ConnectedComponent := Function.Embedding.subtype _
  have sel : Finset.univ.map e=A.K.selected := by
    ext c
    constructor
    · intro m;obtain ⟨v,_,rfl⟩ := Finset.mem_map.mp m;exact v.property
    · intro m;exact Finset.mem_map.mpr ⟨⟨c,m⟩,Finset.mem_univ _,rfl⟩
  exact ten_menu_outlasts_high_stages F paid ten A.K e sel A.units A.upper A.total k menu
    B first C second A.saving A.shortStage A.heightCost A.stageCost

theorem ten_nine_leaf_forbids_mixed_columns (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F)
    (cost:6*highestWidth F.n F.m F.r≤13*A.K.eps+6)
    (heads:0<originalThresholdCount F.n 9 ∨ 0<originalThresholdCount F.m 9)
    (j a b:ℕ) (lo:2≤j) (hi:j≤9) (ra:2≤a) (bl:2≤b) (win:WinsHeight F.n F.m F.r j a b) : False := by
  classical
  let U := A.K.support
  let O := F.G.induce Uᶜ
  have cap (x:↥(Uᶜ:Set F.X)) : Nat.card (O.neighborSet x)≤10 := (induced_neighbor_count_le F.G Uᶜ x).trans
    (((minimal_rank_exact_source F paid).2.2.2.1 x.val).trans_eq ten)
  obtain ⟨B,first⟩ := complete_degree_stage_exists O 10
  obtain ⟨C,second⟩ := complete_degree_stage_exists (O.induce Bᶜ) 9
  have low (x) : Nat.card ((O.induce Bᶜ).neighborSet x)≤9 := Nat.le_of_lt_succ (complete_stage_lowers_cap O 10 B cap first x)
  have last (x) : Nat.card (((O.induce Bᶜ).induce Cᶜ).neighborSet x)≤8 := Nat.le_of_lt_succ
    (complete_stage_lowers_cap _ 9 C low second x)
  have physical := nested_deletion_cap O B C 8 last
  have many := (ten_closed_endpoint_sizes F paid ten A.K).2 (nestedRemoved B C) 9 (by decide)
    (fun x => by have limit := physical x;change Nat.card ((O.induce (nestedRemoved B C)ᶜ).neighborSet x)<9;omega) heads
  rw [nested_removed_card] at many
  have size := ten_nine_leaf_mixed_capacity F paid ten A.K cost heads j a b lo hi ra bl win
  let k := B.ncard+C.ncard
  have menu : SplitCapacities A.units (F.r+k) := split_capacities_of_small _ _ (fun i => by
    have room := Finset.single_le_sum (f:=A.units) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [A.total] at room
    change 2*(F.rank-matchingEdges F.G)≤k at many
    omega)
  have short := A.outlast F paid ten k menu B first C second
  exact (Nat.lt_irrefl k) short

#print axioms PricedTenMenu.outlast
#print axioms ten_nine_leaf_forbids_mixed_columns
end JSP452Audit.StarHost
