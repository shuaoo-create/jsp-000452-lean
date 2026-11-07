import DeletionStep
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finite.Sum

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X Y : Type*} [Finite X] [Finite Y]

private theorem split_card (U : Set (X ⊕ Y)) :
    U.ncard = (Sum.inl ⁻¹' U : Set X).ncard + (Sum.inr ⁻¹' U : Set Y).ncard :=
  (Nat.card_congr (Equiv.subtypeSum (p := fun z => z ∈ U))).trans Nat.card_sum

/-- Restrict one optimal deletion and its actual matching to both disjoint sides. -/
theorem deletionBudget_add_le_sumGraph (G : SimpleGraph X) (H : SimpleGraph Y) (j : ℕ) :
    deletionBudget G j + deletionBudget H j ≤ deletionBudget (G ⊕g H) j := by
  obtain ⟨U,good,attain⟩ := deletionBudget_attained (G ⊕g H) j
  let A : Set X := Sum.inl ⁻¹' U
  let B : Set Y := Sum.inr ⁻¹' U
  let l : G.induce Aᶜ ↪g (G ⊕g H).induce Uᶜ := {
    toFun := fun x => ⟨Sum.inl x.val,x.property⟩
    inj' := fun _ _ e => Subtype.ext (Sum.inl.inj (congrArg (fun x : ↥(Uᶜ : Set (X ⊕ Y)) => x.val) e))
    map_rel_iff' := Iff.rfl }
  let r : H.induce Bᶜ ↪g (G ⊕g H).induce Uᶜ := {
    toFun := fun y => ⟨Sum.inr y.val,y.property⟩
    inj' := fun _ _ e => Subtype.ext (Sum.inr.inj (congrArg (fun x : ↥(Uᶜ : Set (X ⊕ Y)) => x.val) e))
    map_rel_iff' := Iff.rfl }
  have lowA := deletionBudget_le_of_witness G j A (admits_remainder_of_induced_embedding l good)
  have lowB := deletionBudget_le_of_witness H j B (admits_remainder_of_induced_embedding r good)
  exact (Nat.add_le_add lowA lowB).trans_eq ((split_card U).symm.trans attain)

omit [Finite X] [Finite Y] in
/-- Put independent matching remainders side by side, retaining the matched
vertex sets so isolated vertices do not become purported matching vertices. -/
theorem admits_matching_remainder_sum (G : SimpleGraph X) (H : SimpleGraph Y) {j : ℕ}
    (left : admits_matching_remainder G j) (right : admits_matching_remainder H j) :
    admits_matching_remainder (G ⊕g H) j := by
  obtain ⟨M,matchM,capM⟩ := left
  obtain ⟨N,matchN,capN⟩ := right
  let L : (G ⊕g H).Subgraph := {
    verts := fun z => z.elim (· ∈ M.verts) (· ∈ N.verts)
    Adj := (M.spanningCoe ⊕g N.spanningCoe).Adj
    adj_sub := by
      rintro (x | x) (y | y) h
      · exact M.adj_sub h
      · exact h
      · exact h
      · exact N.adj_sub h
    edge_vert := by
      rintro (x | x) (y | y) h
      · exact M.edge_vert h
      · simp at h
      · simp at h
      · exact N.edge_vert h
    symm := ⟨fun _ _ h => h.symm⟩ }
  have matchL : L.IsMatching := by
    rintro (x|y) mem
    · obtain ⟨w,edge,uniq⟩ := matchM mem
      refine ⟨Sum.inl w,edge,?_⟩
      rintro (a|b) h
      · exact congrArg Sum.inl (uniq a h)
      · simp [L] at h
    · obtain ⟨w,edge,uniq⟩ := matchN mem
      refine ⟨Sum.inr w,edge,?_⟩
      rintro (a|b) h
      · simp [L] at h
      · exact congrArg Sum.inr (uniq b h)
  have parts : (G ⊕g H) \ L.spanningCoe = (G \ M.spanningCoe) ⊕g (H \ N.spanningCoe) := by
    ext (x|x) (y|y) <;> simp [L,SimpleGraph.sdiff_adj]
  refine ⟨L,matchL,?_⟩
  rintro (x|y)
  · rw [parts,Nat.card_coe_set_eq,SimpleGraph.neighborSet_sum_inl,
      Set.ncard_image_of_injective _ Sum.inl_injective]
    exact capM x
  · rw [parts,Nat.card_coe_set_eq,SimpleGraph.neighborSet_sum_inr,
      Set.ncard_image_of_injective _ Sum.inr_injective]
    exact capN y

/-- The minimum deletion cost is exactly additive on the true disjoint graph sum.
This also holds for height zero and for empty vertex types. -/
theorem deletionBudget_sumGraph (G : SimpleGraph X) (H : SimpleGraph Y) (j : ℕ) :
    deletionBudget (G ⊕g H) j = deletionBudget G j + deletionBudget H j := by
  refine le_antisymm ?_ (deletionBudget_add_le_sumGraph G H j)
  obtain ⟨A,ga,ha⟩ := deletionBudget_attained G j
  obtain ⟨B,hb,eqB⟩ := deletionBudget_attained H j
  let U : Set (X ⊕ Y) := Sum.elim (· ∈ A) (· ∈ B)
  let e : (G ⊕g H).induce Uᶜ ↪g (G.induce Aᶜ ⊕g H.induce Bᶜ) := {
    toFun := fun z => Equiv.subtypeSum z
    inj' := Equiv.subtypeSum.injective
    map_rel_iff' := by
      rintro ⟨x|y,m⟩ ⟨x'|y',m'⟩ <;> rfl }
  have good := admits_remainder_of_induced_embedding e
    (admits_matching_remainder_sum (G.induce Aᶜ) (H.induce Bᶜ) ga hb)
  have price : U.ncard = A.ncard+B.ncard := split_card U
  exact (deletionBudget_le_of_witness _ j U good).trans_eq (price.trans (congrArg₂ (·+·) ha eqB))

#print axioms deletionBudget_add_le_sumGraph
#print axioms deletionBudget_sumGraph
end JSP452Audit.StarHost
