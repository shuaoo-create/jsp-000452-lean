import PaletteThresholdAssignment
namespace JSP452Audit.StarHost
open SimpleGraph

theorem copy_threshold_supported_order {I X : Type*} [Fintype I] [Finite X]
    (C : SimpleGraph X) (S : Set X) (support : ∀x y,C.Adj x y → x∈S)
    (n : I→ℕ) (y:ℕ) (pos:0<y) (copy : (forest n).IsContained C) :
    headTally n y*(y+1)≤S.ncard := by
  classical
  let k := headTally n y
  obtain ⟨f⟩ := copy
  let g := f.comp (uniform_subforest_copy n y k le_rfl)
  have inside (v:Vertices (fun _:Fin k => y)) : g v∈S := by
    obtain ⟨w,edge⟩ := forest_has_neighbor (fun _:Fin k => y) (fun _ => pos) v
    exact support _ _ (g.toHom.map_rel' edge)
  let send (v:Vertices (fun _:Fin k => y)) : S := ⟨g v,inside v⟩
  have inj : Function.Injective send := fun _ _ eq => g.injective (congrArg Subtype.val eq)
  have bound := Nat.card_le_card_of_injective send inj
  change Nat.card (Σ _:Fin k, Fin (y+1))≤Nat.card S at bound
  simpa [Nat.card_sigma,k] using bound

theorem head_tally_one {I:Type*} [Fintype I] (n:I→ℕ) (pos:∀i,1≤n i) : headTally n 1=Fintype.card I := by
  simp [headTally,pos]

theorem copied_head_degree_cap {I X : Type*} [Fintype I] [Finite X]
    (C : SimpleGraph X) (n:I→ℕ) (copy:(forest n).IsContained C) (h:ℕ)
    (cap:∀v,Nat.card (C.neighborSet v)≤h) : ∀i,n i≤h := by
  obtain ⟨f⟩ := copy
  intro i
  let e : Fin 1 ↪ I := ⟨fun _ => i,fun _ _ _ => Subsingleton.elim _ _⟩
  let g := f.comp (subforestCopy (fun _:Fin 1 => n i) n e (fun _ => le_rfl))
  exact (star_copy_center_degree C g).trans (cap _)

theorem bottom_forest_preserves {X Y : Type*} (C:SimpleGraph Y) (h:ℕ) :
    PreservesSmallForests (⊥:SimpleGraph X) C h := by
  intro I _ n pos _ copy
  obtain ⟨f⟩ := copy
  have empty (v:Vertices n) : False := by
    obtain ⟨w,edge⟩ := forest_has_neighbor n pos v
    exact f.toHom.map_rel' edge
  let send (v:Vertices n) : Y := (empty v).elim
  refine ⟨{toHom := {toFun := send,map_rel' := ?_},injective' := fun v _ _ => (empty v).elim}⟩
  intro v w adj
  exact (empty v).elim

#print axioms copy_threshold_supported_order
#print axioms head_tally_one
#print axioms copied_head_degree_cap
#print axioms bottom_forest_preserves
end JSP452Audit.StarHost
