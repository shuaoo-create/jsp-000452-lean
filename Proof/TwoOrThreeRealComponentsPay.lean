import SixMultiComponentCapacityBounds
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem multi_component_history_contradiction (j h P L b C k M:ℕ)
    (size:j=2 ∨ j=3) (width:h≤j+1) (step:2*k≤P) (halves:2*M≤P) (nested:b≤C)
    (shadow:L+j≤P+b+(2*h+10)/3)
    (alt:k≤C ∨ L≤C+M+(h-1))
    (five:P+3*j+1+min k C+min k b≤k+L+h)
    (six:3*j+1+min k C+min k b≤2*k+h) : False := by
  by_cases full : k≤b
  · rw [min_eq_left full,min_eq_left (full.trans nested)] at six
    rcases size with s|s <;> omega
  have scarce := Nat.le_of_not_ge full
  rw [min_eq_right scarce] at five
  by_cases enough : k≤C
  · rw [min_eq_left enough] at five
    rcases size with s|s <;> omega
  · rw [min_eq_right (Nat.le_of_not_ge enough)] at five
    have unreachable := alt.resolve_left enough
    rcases size with s|s <;> omega

theorem strict_six_small_menu_impossible {I:Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (six:diagonal F.n F.m (F.r+2)-1=6)
    (e:I ↪ F.G.ConnectedComponent) (actual:∀i,e i∈oddRegularComponents F.G 6)
    (size:Fintype.card I=2 ∨ Fintype.card I=3) (width:highestWidth F.n F.m F.r≤Fintype.card I+1)
    (k:ℕ) (step:2*k≤∑i,matchingEdges (e i).toSimpleGraph)
    (menu:SplitCapacities (fun i => matchingEdges (e i).toSimpleGraph) (F.r+k)) : False := by
  classical
  let T := Finset.univ.map e
  let U := componentVertices F.G T
  let O := F.G.induce Uᶜ
  let P := matchingEdges (F.G.induce U)
  let d := F.rank-matchingEdges F.G
  let h := highestWidth F.n F.m F.r
  let L := widthAt F.n F.m F.r 6
  let M := chosenSlots F.G T 3
  have j : T.card=Fintype.card I := by simp [T]
  have ts : T.card=2 ∨ T.card=3 := j ▸ size
  have th : h≤T.card+1 := by rw [j];exact width
  have member (c) (mem:c∈T) : c∈oddRegularComponents F.G 6 := by obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp mem;exact actual i
  have sum := (component_union_accounts F.G T).2.1
  change P=∑c∈Finset.univ.map e,matchingEdges c.toSimpleGraph at sum
  rw [Finset.sum_map] at sum
  have ks : 2*k≤P := step.trans_eq sum.symm
  have limit := strict_two_or_three_capacity_total F paid six T member ts th
  change P≤3*d at limit
  obtain ⟨H⟩ := six_five_four_history_exists O
  obtain ⟨floor,five,small⟩ := strict_exterior_history_cut_bounds F paid six T member H
  change 2*d≤H.fourCut.ncard at floor
  have fit : k≤H.fourCut.ncard := by omega
  have alt : k≤H.fiveCut.ncard ∨ L≤H.fiveCut.ncard+M+(h-1) := by
    by_cases big : 0<originalThresholdCount F.n 5 ∨ 0<originalThresholdCount F.m 5
    · have free := five big
      change 2*d≤H.fiveCut.ncard at free
      exact Or.inl (by omega)
    · right
      apply small
      · intro i;by_contra! exceed
        have pos := (original_threshold_prefix F.n F.hn 5 i).mp exceed
        exact big (Or.inl (by omega))
      · intro i;by_contra! exceed
        have pos := (original_threshold_prefix F.m F.hm 5 i).mp exceed
        exact big (Or.inr (by omega))
  obtain ⟨p5,p6⟩ := strict_six_menu_history_price F paid six e actual k menu H fit
  rw [←sum] at p5
  have halves := (strict_chosen_slot_totals F paid six T member).2
  have short := strict_six_short_shadow F paid six T member H.six H.stageSix
  rw [j] at short
  have nested : H.six.ncard≤H.fiveCut.ncard := by rw [H.cut_counts.1];omega
  exact multi_component_history_contradiction (Fintype.card I) h P L H.six.ncard H.fiveCut.ncard k M size width ks halves nested short alt p5 p6

#print axioms multi_component_history_contradiction
#print axioms strict_six_small_menu_impossible
end JSP452Audit.StarHost
