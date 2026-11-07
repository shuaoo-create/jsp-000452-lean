import CubicComponentGroups
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X I : Type*} [Fintype X] [Fintype I]

private theorem no_site_neighbor (G:SimpleGraph X) (U:Set X) (c:(G.induce U).ConnectedComponent)
    (R:Set X) (sub:R⊆U) (apart:Disjoint R (cubicWhiteSite G U c)) {x:X} (hx:x∈cubicWhiteSite G U c) :
    fourWhiteDegree G R x=0 := by
  have none : G.neighborSet x∩R=∅ := Set.eq_empty_iff_forall_notMem.mpr (fun w h =>
    Set.disjoint_left.mp apart h.2 (site_closed_adj G U c hx (sub h.2) h.1))
  unfold fourWhiteDegree;rw [none,Set.ncard_empty]

namespace CubicPairFamily
variable (P:CubicPairFamily X I)

theorem square_without_outgoing_pair (G:SimpleGraph X) (U:Set X) (c:(G.induce U).ConnectedComponent)
    (square:CubicSquareSite G U c) (cap:∀x∈U,fourWhiteDegree G U x+P.degree U x≤3)
    (closed:∀j∈P.active U,P.left j∈cubicWhiteSite G U c ↔ P.right j∈cubicWhiteSite G U c) :
    P.PaidRemoval G U := by
  classical
  let T := cubicWhiteSite G U c
  let R := U\T
  have sub : T⊆U := site_in_white G U c
  have pieces : P.active U=P.active R∪P.active T := by
    ext j
    constructor
    · intro mem
      obtain ⟨l,r⟩ := (P.mem_active U j).1 mem
      by_cases cut:P.left j∈T
      · exact Finset.mem_union_right _ ((P.mem_active T j).2 ⟨cut,(closed j mem).1 cut⟩)
      · exact Finset.mem_union_left _ ((P.mem_active R j).2 ⟨⟨l,cut⟩,⟨r,fun yes => cut ((closed j mem).2 yes)⟩⟩)
    · intro mem
      rcases Finset.mem_union.mp mem with outer|inner
      · exact P.active_mono Set.sdiff_subset outer
      · exact P.active_mono sub inner
  have dis : Disjoint (P.active R) (P.active T) := Finset.disjoint_left.mpr (fun j r t =>
    ((P.mem_active R j).1 r).1.2 ((P.mem_active T j).1 t).1)
  have pairPrice := congrArg Finset.card pieces
  rw [Finset.card_union_of_disjoint dis] at pairPrice
  have price := P.isolated_four_cost G U T sub square.size square.degree (site_cross_zero G U c)
    pairPrice (fun x hx => cap x (sub hx))
  have pos : T.Nonempty := (Set.ncard_pos (Set.toFinite _)).1 (by rw [square.size];decide)
  obtain ⟨x,hx⟩ := pos
  obtain ⟨w,_,covers⟩ := square.repair x hx
  let S : Set X := {x,w}
  have size : S.ncard≤2 := by simpa [S] using Set.ncard_insert_le x ({w}:Set X)
  refine ⟨T,S,sub,⟨x,hx⟩,?_,?_⟩
  · intro y hy;by_cases same:y=x
    · exact Or.inl (Or.inl same)
    · rcases covers y hy same with isW|adj
      · exact Or.inl (Or.inr isW)
      · exact Or.inr ⟨w,Or.inr rfl,adj⟩
  · change 5*S.ncard+P.residualCost G U≤5*T.ncard+P.residualCost G R
    change P.residualCost G U≤P.residualCost G R+10 at price
    have four : T.ncard=4 := square.size
    omega

/-- One labelled pair actually touches the square at p and a white
vertex u of ordinary white degree at most one. Its blue witness covers both. -/
theorem square_to_low_vertex (G:SimpleGraph X) (U:Set X) (c:(G.induce U).ConnectedComponent)
    (square:CubicSquareSite G U c) (cap:∀x∈U,fourWhiteDegree G U x+P.degree U x≤3)
    (p u w:X) (pT:p∈cubicWhiteSite G U c) (uU:u∈U) (uT:u∉cubicWhiteSite G U c)
    (low:fourWhiteDegree G U u≤1) (pw:G.Adj p w) (uw:G.Adj u w)
    (pair:0<(P.active (insert u (cubicWhiteSite G U c))).card) : P.PaidRemoval G U := by
  classical
  let T := cubicWhiteSite G U c
  let W := insert u T
  let R := U\W
  have sizeT : T.ncard=4 := square.size
  have size : W.ncard=5 := by dsimp [W];rw [Set.ncard_insert_of_notMem uT,sizeT]
  have sub : W⊆U := Set.insert_subset uU (site_in_white G U c)
  have apart : Disjoint R T := Set.disjoint_left.mpr (fun _ r t => r.2 (Set.mem_insert_of_mem _ t))
  have gain (x:X) (hx:x∈W) : fourWhiteDegree G R x≤(if u=x then 1 else 0) := by
    by_cases eq:u=x
    · subst x
      rw [if_pos rfl]
      exact (Set.ncard_le_ncard (Set.inter_subset_inter_right _ (show R⊆U from Set.sdiff_subset))).trans low
    · have xt : x∈T := hx.resolve_left (Ne.symm eq)
      rw [if_neg eq,no_site_neighbor G U c R Set.sdiff_subset apart xt]
  have cross := four_sum_mono W _ _ gain
  rw [four_sum_cross,four_sum_single_label W u (Set.mem_insert _ _)] at cross
  obtain ⟨z,_,hit⟩ := square.repair p pT
  let S : Set X := {w,z}
  have ss : S.ncard≤2 := by simpa [S] using Set.ncard_insert_le w ({z}:Set X)
  apply P.removal_of_cross_price G U W S sub ⟨u,Set.mem_insert _ _⟩ _ cap _
  · intro x hx
    rcases hx with same|inT
    · exact Or.inr ⟨w,Or.inl rfl,same.symm ▸ uw⟩
    by_cases same:x=p
    · exact Or.inr ⟨w,Or.inl rfl,same.symm ▸ pw⟩
    rcases hit x inT same with eq|edge
    · exact Or.inl (Or.inr eq)
    · exact Or.inr ⟨z,Or.inr rfl,edge⟩
  · change 0<(P.active W).card at pair
    change crossCount G W (U\W)≤1 at cross
    omega

end CubicPairFamily
#print axioms CubicPairFamily.square_without_outgoing_pair
#print axioms CubicPairFamily.square_to_low_vertex
end JSP452Audit.StarHost
