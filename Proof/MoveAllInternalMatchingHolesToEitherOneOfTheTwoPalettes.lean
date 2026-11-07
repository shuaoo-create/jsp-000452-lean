import OnlyOriginalPortFreeOddRegularComponentsCanCostAnInternalHole
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem real_hole_palette_split {B:Type u} [Finite B] (C:SimpleGraph B) (D p q x y:ℕ) (pos:0<D)
    (sum:D=p+q) (cap:∀v,Nat.card (C.neighborSet v)≤D) (red:p<x) (blue:q<y) :
    ∃R:SimpleGraph B,R≤C ∧ UniformPackCap R x 0 ∧ UniformPackCap (C \ R) y (minimumExposure C D) := by
  classical
  obtain ⟨U,remainderWitness,num⟩ := deletionBudget_attained C D
  obtain ⟨F,sub,split⟩ := degree_split_of_exists_matching_remainder (C.induce Uᶜ) D p q sum pos remainderWitness
  let R := setRestoreRed C U ∅ F
  have cover : U=∅∪U := by simp
  obtain ⟨one,two⟩ := set_restore_edge_covers C U ∅ U cover F
  have left := set_restore_lift_cap U F p (fun v => (split v).1)
  have right := set_restore_lift_cap U ((C.induce Uᶜ) \ F) q (fun v => (split v).2)
  refine ⟨R,setRestoreRed_le C U ∅ F sub,?_,?_⟩
  · intro k copy
    have tally := count_large_of_edge_cover R _ ∅ p (fun _:Fin k => x) one left copy
    simpa [show p+1≤x by omega] using tally
  · intro k copy
    have tally := count_large_of_edge_cover (C \ R) _ U q (fun _:Fin k => y) two right copy
    have sz : k≤U.ncard := by simpa [show q+1≤y by omega] using tally
    exact sz.trans (num.le.trans (deletionBudget_le_minimumExposure C D pos cap))

theorem near_top_actual_palettes {B:Type u} [Finite B] (C:SimpleGraph B) (D p q x y:ℕ) (pos:0<D)
    (sum:D=p+q) (cap:∀v,Nat.card (C.neighborSet v)≤D) (red:p<x) (blue:q<y) :
    (∃R:SimpleGraph B,R≤C ∧ UniformPackCap R x 0 ∧ UniformPackCap (C \ R) y (minimumExposure C D)) ∧
    (∃R:SimpleGraph B,R≤C ∧ UniformPackCap R x (minimumExposure C D) ∧ UniformPackCap (C \ R) y 0) := by
  refine ⟨real_hole_palette_split C D p q x y pos sum cap red blue,?_⟩
  obtain ⟨R,sub,a,b⟩ := real_hole_palette_split C D q p y x pos (by omega) cap blue red
  have inv : C \ (C \ R)=R := by
    ext v w;simp only [sdiff_adj]
    have incl : R.Adj v w → C.Adj v w := fun e => sub e
    tauto
  exact ⟨C \ R,sdiff_le,b,inv.symm ▸ a⟩

#print axioms real_hole_palette_split
#print axioms near_top_actual_palettes
end JSP452Audit.StarHost
