import MixedUniformColumnsAtTheSixExposureBoundary
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem width_six_nine_leaf_forbids_mixed (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F)
    (six:highestWidth F.n F.m F.r=6) (eps:A.K.eps=2)
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
  have size := ten_width_six_mixed_capacity F paid ten A.K six eps heads j a b lo hi ra bl win
  let k := B.ncard+C.ncard
  have menu : SplitCapacities A.units (F.r+k) := split_capacities_of_small _ _ (fun i => by
    have room := Finset.single_le_sum (f:=A.units) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [A.total] at room
    change 2*(F.rank-matchingEdges F.G)≤k at many
    omega)
  have short := A.outlast F paid ten k menu B first C second
  exact (Nat.lt_irrefl k) short


theorem width_six_regular_lists_at_most_eight (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F)
    (six:highestWidth F.n F.m F.r=6) (eps:A.K.eps=2) : (∀i,F.n i≤8) ∧ (∀j,F.m j≤8) := by
  have no : ¬(0<originalThresholdCount F.n 9 ∨ 0<originalThresholdCount F.m 9) := by
    intro heads
    have lengths := (ten_closed_endpoint_sizes F paid ten A.K).1
    have dpos := (minimal_strict_source_deficit F paid).2.2
    have axes (j:ℕ) (lo:1≤j) (hi:j≤9) : ∃x y,WinsHeight F.n F.m F.r j x y ∧ (x=1 ∨ y=1) := by
      have floor := lower_axis_at_any_head (r:=F.r) F.n F.m F.hn F.hm F.pn F.pm heads F.hs F.ht lo hi
      have live : 0<widthAt F.n F.m F.r j := by omega
      obtain ⟨x,y,xp,yp,ht,rr,bb,wide⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm lo live
      have win : WinsHeight F.n F.m F.r j x y := ⟨xp,yp,ht,rr,bb,wide⟩
      refine ⟨x,y,win,?_⟩
      by_contra! neither
      exact width_six_nine_leaf_forbids_mixed F paid ten A six eps heads j x y (by omega) hi (by omega) (by omega) win
    exact ten_all_axes_contradict_regular_menu F paid ten A axes
  constructor
  · intro i;by_contra! big
    have mem := (original_threshold_prefix F.n F.hn 9 i).mp big
    exact no (Or.inl (by omega))
  · intro j;by_contra! big
    have mem := (original_threshold_prefix F.m F.hm 9 j).mp big
    exact no (Or.inr (by omega))


theorem width_six_conservative_capacity (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F) (six:highestWidth F.n F.m F.r=6)
    (eps:A.K.eps=2) (slack:1≤A.K.slack) : A.K.P≤2*(F.rank-matchingEdges F.G) := by
  obtain ⟨red,blue⟩ := width_six_regular_lists_at_most_eight F paid ten A six eps
  have price := ten_regular_exterior_slot_deficit F paid ten A.K 3 (fun i => by have := red i;omega) (fun i => by have := blue i;omega)
  have slots := ten_regular_slot_volume A.K 3
  omega
#print axioms width_six_nine_leaf_forbids_mixed
#print axioms width_six_regular_lists_at_most_eight
#print axioms width_six_conservative_capacity
end JSP452Audit.StarHost
