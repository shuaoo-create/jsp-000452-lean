import ZhaoModels
import SmallAlphaPerfect

set_option synthInstance.maxSize 1024

namespace JSP452Audit.StarHost
open SimpleGraph

private abbrev V := ZhaoVertex 2
private abbrev L (i : Fin 4) : V := zhaoLeft i
private abbrev R (i : Fin 4) : V := zhaoRight i
private abbrev C := (zhaoGraph 2)ᶜ

private theorem neighbor_count_filter {X : Type*} [Fintype X] (G : SimpleGraph X)
    [DecidableRel G.Adj] (x : X) :
    Nat.card (G.neighborSet x) = (Finset.univ.filter (fun y => G.Adj x y)).card := by
  change Nat.card {y // G.Adj x y} = _
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem zhao_four_complement_regular : ∀ x, Nat.card (C.neighborSet x) = 4 := by
  have table : ∀ x : V, (Finset.univ.filter (fun y => C.Adj x y)).card = 4 := by decide
  exact fun x => (neighbor_count_filter C x).trans (table x)

/-- The three original labels are z, L0, R1. -/
theorem zhao_four_complement_independent_triple :
    ∃ x y z : ZhaoVertex 2, x≠y ∧ x≠z ∧ y≠z ∧ ¬C.Adj x y ∧ ¬C.Adj x z ∧ ¬C.Adj y z := by
  exact ⟨none,L 0,R 1,by decide,by decide,by decide,by decide,by decide,by decide⟩

private def cut : Set V := {L 2,R 2}
private instance (x : V) : Decidable (x ∈ cutᶜ) :=
  inferInstanceAs (Decidable (¬ (x=L 2 ∨ x=R 2)))
private abbrev Kept := ↥(cutᶜ : Set V)
private abbrev H := C.induce cutᶜ

/-- Both orientations of the three retained original matching edges. -/
private def pairs : Finset (V × V) :=
  {(L 0,R 0),(R 0,L 0),(L 1,L 3),(L 3,L 1),(R 1,R 3),(R 3,R 1)}

private theorem pairEdges : ∀ x y : Kept, (x.val,y.val)∈pairs → H.Adj x y := by decide
private theorem pairSymm : ∀ x y : Kept, (x.val,y.val)∈pairs → (y.val,x.val)∈pairs := by decide
private theorem pairUnique : ∀ x y z : Kept, (x.val,y.val)∈pairs → (x.val,z.val)∈pairs → y=z := by decide

private def tableMatching : H.Subgraph where
  verts := {x | ∃ y : Kept, (x.val,y.val)∈pairs}
  Adj x y := (x.val,y.val)∈pairs
  adj_sub := fun {x y} h => pairEdges x y h
  edge_vert := fun {_ y} h => ⟨y,h⟩
  symm := ⟨pairSymm⟩

private theorem table_is_matching : tableMatching.IsMatching := by
  intro x used
  obtain ⟨y,edge⟩ := used
  exact ⟨y,edge,fun z adj => pairUnique x z y adj edge⟩

private def cleanAdj (x y : Kept) : Prop := H.Adj x y ∧ (x.val,y.val)∉pairs
private instance (x y : Kept) : Decidable (cleanAdj x y) :=
  inferInstanceAs (Decidable (H.Adj x y ∧ (x.val,y.val)∉pairs))

private theorem leftover_degree (x : Kept) :
    Nat.card ((H \ tableMatching.spanningCoe).neighborSet x) ≤ 2 := by
  have table : ∀ v : Kept, (Finset.univ.filter (cleanAdj v)).card ≤ 2 := by decide
  change Nat.card { y // cleanAdj x y } ≤ 2
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  exact table x

theorem zhao_four_complement_deletion : deletionBudget (zhaoGraph 2)ᶜ 3 ≤ 2 := by
  have witness : admits_matching_remainder H 3 :=
    ⟨tableMatching,table_is_matching,leftover_degree⟩
  have bound := deletionBudget_le_of_witness C 3 cut witness
  have count : cut.ncard=2 := Set.ncard_eq_two.mpr ⟨L 2,R 2,by decide,rfl⟩
  exact bound.trans_eq count

theorem zhao_four_complement_certificate :
    (∀ x, Nat.card ((zhaoGraph 2)ᶜ.neighborSet x) = 4) ∧
    ¬NoIndependentTriple (zhaoGraph 2)ᶜ ∧ deletionBudget (zhaoGraph 2)ᶜ 3 ≤ 2 := by
  refine ⟨zhao_four_complement_regular,?_,zhao_four_complement_deletion⟩
  rintro small
  obtain ⟨x,y,z,xy,xz,yz,nxy,nxz,nyz⟩ := zhao_four_complement_independent_triple
  exact (small x y z xy xz yz).elim nxy (fun h => h.elim nxz nyz)

#print axioms zhao_four_complement_independent_triple
#print axioms zhao_four_complement_certificate
end JSP452Audit.StarHost
