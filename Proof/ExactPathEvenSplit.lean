import RankSplitDef

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Both color classes meet their complementary matching budgets on the same host. -/
def ExactRankSplit {X : Type*} [Finite X] (G : SimpleGraph X) : Prop :=
  ∀ u : ℕ, u ≤ matchingEdges G → ∃ R : SimpleGraph X, R ≤ G ∧
    matchingEdges R ≤ u ∧ matchingEdges (G \ R) ≤ matchingEdges G - u

/-- Charge each edge of a maximum matching to one of its ends in the cover.
The matching ensures that two different edges cannot receive the same label. -/
theorem matchingEdges_le_cover_card {X : Type*} [Finite X] (G : SimpleGraph X) (U : Set X)
    (cover : ∀ ⦃x y⦄, G.Adj x y → x ∈ U ∨ y ∈ U) : matchingEdges G ≤ U.ncard := by
  classical
  obtain ⟨M,hm,largest⟩ := exists_maximum_matching G
  have endpoint (e : M.edgeSet) : ∃ (x : U) (y : X), M.Adj x.val y ∧ e.val=s(x.val,y) := by
    obtain ⟨e,member⟩ := e
    induction e using Sym2.inductionOn with
    | _ x y =>
      have edge : M.Adj x y := member
      rcases cover (M.adj_sub edge) with hx | hy
      · exact ⟨⟨x,hx⟩,y,edge,rfl⟩
      · exact ⟨⟨y,hy⟩,x,edge.symm,Sym2.eq_swap⟩
  choose controller partner adjacent label using endpoint
  have inj : Function.Injective controller := by
    intro a b same
    have other := hm.eq_of_adj_left (adjacent a) (same ▸ adjacent b)
    exact Subtype.ext ((label a).trans (by rw [same,other,label b]))
  rw [← largest,← Nat.card_coe_set_eq,← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective controller inj

/-- A cover whose size equals the matching number can be partitioned between
the colors. This includes the empty cover and either empty color class. -/
theorem exactRankSplit_of_cover {X : Type*} [Finite X] (G : SimpleGraph X) (U : Set X)
    (size : U.ncard = matchingEdges G)
    (cover : ∀ ⦃x y⦄, G.Adj x y → x ∈ U ∨ y ∈ U) : ExactRankSplit G := by
  intro u h
  obtain ⟨A,subset,cardA⟩ := Set.exists_subset_card_eq (h.trans_eq size.symm)
  let R : SimpleGraph X := {
    Adj := fun x y => G.Adj x y ∧ (x∈A ∨ y∈A)
    symm := ⟨fun _ _ edge => ⟨edge.1.symm,edge.2.symm⟩⟩
    loopless := ⟨fun x edge => G.loopless.irrefl x edge.1⟩ }
  refine ⟨R,fun _ _ edge => edge.1,?_,?_⟩
  · exact (matchingEdges_le_cover_card R A (fun _ _ h => h.2)).trans_eq cardA
  · have covered : ∀ ⦃x y⦄, (G \ R).Adj x y → x∈U\A ∨ y∈U\A := by
      intro x y edge
      rcases cover edge.1 with hx | hy
      · exact Or.inl ⟨hx,fun ha => edge.2 ⟨edge.1,Or.inl ha⟩⟩
      · exact Or.inr ⟨hy,fun ha => edge.2 ⟨edge.1,Or.inr ha⟩⟩
    simpa [Set.ncard_sdiff subset,size,cardA] using matchingEdges_le_cover_card _ _ covered

private def oddLabels (n : ℕ) : Set (Fin n) := {v | v.val % 2 = 1}

private theorem oddLabels_card (n : ℕ) : (oddLabels n).ncard = n/2 := by
  let e : oddLabels n ≃ Fin (n/2) :=
    { toFun x := ⟨x.val.val/2,by
        have lt := x.val.isLt
        have parity : x.val.val % 2 = 1 := x.property
        omega⟩
      invFun i := ⟨⟨2*i.val+1,by have lt := i.isLt; omega⟩,by change (2*i.val+1)%2=1; omega⟩
      left_inv x := Subtype.ext (Fin.ext (by
        have parity : x.val.val % 2 = 1 := x.property
        change 2*(x.val.val/2)+1=x.val.val
        omega))
      right_inv i := Fin.ext (by change (2*i.val+1)/2=i.val; omega) }
  exact (Nat.card_congr e).trans (Nat.card_fin _)

/-- The odd-numbered vertices are a minimum-size cover of the indexed path. -/
theorem exactRankSplit_pathGraph (n : ℕ) : ExactRankSplit (pathGraph n) := by
  apply exactRankSplit_of_cover _ (oddLabels n) ((oddLabels_card n).trans (pathGraph_matchingEdges n).symm)
  intro x y edge
  change x.val % 2 = 1 ∨ y.val % 2 = 1
  rcases pathGraph_adj.mp edge with h | h <;> omega

private theorem odd_end_of_cycle_step (k : ℕ) (x y : Fin (2*k)) (step : (x-y).val = 1) :
    x.val%2=1 ∨ y.val%2=1 := by
  by_cases le : y ≤ x
  · rw [Fin.sub_val_of_le le] at step
    omega
  · have lt : x.val < y.val := Nat.lt_of_not_ge le
    have bound := y.isLt
    have wrap : 2*k - y.val + x.val < 2*k := by omega
    rw [Fin.val_sub,Nat.mod_eq_of_lt wrap] at step
    omega

/-- Even cyclic order preserves the two parities across the closing edge. -/
theorem exactRankSplit_even_cycleGraph (k : ℕ) : ExactRankSplit (cycleGraph (2*k)) := by
  apply exactRankSplit_of_cover _ (oddLabels (2*k))
    ((oddLabels_card _).trans (cycleGraph_matchingEdges _).symm)
  intro x y edge
  change x.val%2=1 ∨ y.val%2=1
  rcases cycleGraph_adj'.mp edge with step | step
  · exact odd_end_of_cycle_step k x y step
  · exact (odd_end_of_cycle_step k y x step).symm

#print axioms exactRankSplit_of_cover
#print axioms exactRankSplit_pathGraph
#print axioms exactRankSplit_even_cycleGraph
end JSP452Audit.StarHost
