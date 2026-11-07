import FinalDescentLengths
import FiniteHostReserveAndRows
import DegreeTwoSplit
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit
namespace JSP452Audit.StarHost
open SimpleGraph

/-- A positive graph contained in a red summand plus isolated vertices has
an actual copy inside that red summand. -/
theorem copy_in_left_summand {X Y Z : Type*} (C : SimpleGraph X) (T : SimpleGraph Z)
    (positive : ∀z,∃w,T.Adj z w) (copy : T.IsContained (C ⊕g (⊥ : SimpleGraph Y))) :
    T.IsContained C := by
  classical
  obtain ⟨f⟩ := copy
  have land (z:Z) : ∃x:X,Sum.inl x=f z := by
    cases h : f z with
    | inl x => exact ⟨x,rfl⟩
    | inr y =>
      obtain ⟨w,e⟩ := positive z
      have image := f.toHom.map_adj e
      change (C ⊕g (⊥ : SimpleGraph Y)).Adj (f z) (f w) at image
      rw [h] at image
      cases k : f w with
      | inl x => exact (not_adj_sum_inl_inr _ _ ((k ▸ image).symm)).elim
      | inr v => rw [k] at image;exact image.elim
  let g (z:Z) := (land z).choose
  have eq (z:Z) : Sum.inl (g z)=f z := (land z).choose_spec
  refine ⟨{toHom := {toFun := g,map_rel' := ?_},injective' := ?_}⟩
  · intro a b adj
    have e := f.toHom.map_adj adj
    change (C ⊕g (⊥ : SimpleGraph Y)).Adj (f a) (f b) at e
    rw [←eq,←eq] at e
    exact e
  · intro a b same
    exact f.injective ((eq a).symm.trans ((congrArg Sum.inl same).trans (eq b)))

/-- The left endpoint of the shifted forcing row produces the entire original
red forest whenever the all-blue second summand cannot hold the blue suffix. -/
theorem sum_row_forces_whole_left {X Y : Type*} [Finite X] [Finite Y]
    (C : SimpleGraph X) (B : SimpleGraph Y) {s t r : ℕ} (hs : 0<s)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow (C ⊕g B) s t (padDemand n) (padDemand m) r)
    (short : matchingEdges B+r<t) : (forest n).IsContained C := by
  have force := row 0 r s (t-r) (by omega) (by omega) (by omega) hs (by omega)
  obtain ⟨sub,comp⟩ := JSP452Audit.StarHost.sum_colors (le_refl C) (bot_le : (⊥ : SimpleGraph Y)≤B)
  rcases force _ sub with red|blue
  · have origin : (fun i : Fin s => padDemand n (0+i.val))=n := by
      funext i;simp [padDemand,i.isLt]
    change (forest (fun i : Fin s => padDemand n (0+i.val))).IsContained _ at red
    rw [origin] at red
    exact copy_in_left_summand C (forest n) (forest_has_neighbor n pn) red
  · have bound := forest_copy_matching _ (fun i : Fin (t-r) => padDemand m (r+i.val))
      (fun i => pad_positive m pm _ (by have hi:=i.isLt;omega)) blue
    rw [comp,sdiff_self,sdiff_bot,matchingEdges_sumGraph,matchingEdges_bot,Fintype.card_fin] at bound
    omega

theorem swap_positive_forcing_row {X : Type*} (G : SimpleGraph X) {s t r : ℕ} (n m : ℕ→ℕ)
    (row : ForcingRow G s t n m r) : ForcingRow G t s m n r := by
  intro i j l q hr hl hq pl pq
  exact forces_swap (row j i q l (by omega) hq hl pq pl)

#print axioms copy_in_left_summand
#print axioms sum_row_forces_whole_left
#print axioms swap_positive_forcing_row
end JSP452Audit.StarHost
