import ThreeVerticesPerTouchedStar
namespace JSP452Audit.StarHost
open SimpleGraph

theorem trim_touched_uniform_copy {X:Type*} [Finite X] (R P:SimpleGraph X) (u a M:ℕ)
    (f:(forest (fun _:Fin u => a)).Copy (R⊔P))
    (damage:(touchedStars R P (fun _:Fin u => a) f).ncard≤M) :
    (forest (fun _:Fin (u-M) => a)).IsContained R := by
  classical
  let n := fun _:Fin u => a
  let B := touchedStars R P n f
  let _ := Fintype.ofFinite ↥(Bᶜ:Set (Fin u))
  have total := Set.ncard_add_ncard_compl B
  rw [Nat.card_fin] at total
  change B.ncard≤M at damage
  have fit : Fintype.card (Fin (u-M))≤Fintype.card ↥(Bᶜ:Set (Fin u)) := by
    rw [Fintype.card_fin,←Nat.card_eq_fintype_card];change u-M≤Bᶜ.ncard;omega
  obtain ⟨pick⟩ := Function.Embedding.nonempty_of_card_le fit
  let labels := pick.trans (Function.Embedding.subtype (·∈Bᶜ))
  let sel := subforestCopy (fun _:Fin (u-M) => a) n labels (fun _ => le_rfl)
  refine ⟨{toHom := {toFun := fun x => f (sel x),map_rel' := ?_},injective' := f.injective.comp sel.injective}⟩
  intro x y e
  have good : (sel x).1∉B := (pick x.1).property
  exact untouched_star_adjacency R P n f good (sel.toHom.map_adj e)

theorem uniform_after_restoring_red {X:Type*} [Finite X] (G P:SimpleGraph X) (sub:P≤G)
    (a b u v M:ℕ)
    (bound:∀R:SimpleGraph X,R≤G \ P → ∀f:(forest (fun _:Fin u => a)).Copy (R⊔P),
      (touchedStars R P (fun _:Fin u => a) f).ncard≤M)
    (force:Forces G (forest (fun _:Fin u => a)) (forest (fun _:Fin v => b))) :
    Forces (G \ P) (forest (fun _:Fin (u-M) => a)) (forest (fun _:Fin v => b)) := by
  intro R less
  have valid : R⊔P≤G := sup_le (less.trans sdiff_le) sub
  have blue : G \ (R⊔P)≤(G \ P) \ R :=
    fun _ _ edge => ⟨⟨edge.1,fun hit => edge.2 (Or.inr hit)⟩,fun hit => edge.2 (Or.inl hit)⟩
  rcases force _ valid with red|copy
  · obtain ⟨f⟩ := red
    exact Or.inl (trim_touched_uniform_copy R P u a M f (bound R less f))
  · exact Or.inr (copy.mono_right blue)

#print axioms trim_touched_uniform_copy
#print axioms uniform_after_restoring_red
end JSP452Audit.StarHost
