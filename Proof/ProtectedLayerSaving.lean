import ProtectedBudgetSplit
import OneLayerPaysPortDeficit
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- To compare returning protected vertices with deleting them, cut all
their boundary roots. The unaffected exterior embeds back into G-I. -/
theorem protected_budget_comparison (G : SimpleGraph X) (I W L R : Set X) (j : ℕ)
    (removed : I⊆L∪W)
    (boundary : ∀x∈W,∀ y,G.Adj x y → y∉W → y∈R) :
    deletionBudget G j ≤ L.ncard+R.ncard+deletionBudget (G.induce W) j+deletionBudget (G.induce Iᶜ) j := by
  let K := G.induce (L∪R)ᶜ
  let C : Set ↥((L∪R)ᶜ : Set X) := {v | v.val∈W}
  have sep : ∀x∈C,∀y∈Cᶜ,¬K.Adj x y := by
    intro x hx y hy edge
    exact y.property (Or.inr (boundary x.val hx y.val edge hy))
  have split := deletionBudget_split_cut K C j sep
  let left : K.induce C ↪g G.induce W := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    inj' := fun _ _ eq => Subtype.ext (Subtype.ext (congrArg (fun w : W => w.val) eq))
    map_rel_iff' := Iff.rfl }
  let right : K.induce Cᶜ ↪g G.induce Iᶜ := {
    toFun := fun x => ⟨x.val.val,fun hx =>
      (removed hx).elim (fun l => x.val.property (Or.inl l)) (fun w => x.property w)⟩
    inj' := fun _ _ eq => Subtype.ext (Subtype.ext (congrArg (fun w : ↥(Iᶜ : Set X) => w.val) eq))
    map_rel_iff' := Iff.rfl }
  have a := deletionBudget_mono_embedding left j
  have b := deletionBudget_mono_embedding right j
  have del := deletion_le_after_cut_add G (L∪R) j
  change deletionBudget G j ≤ (L∪R).ncard+deletionBudget K j at del
  have count := Set.ncard_union_le L R
  omega

theorem protected_layer_saving (G : SimpleGraph X) (I W R : Set X) (j h : ℕ)
    (boundary : ∀x∈W,∀ y,G.Adj x y → y∉W → y∈R)
    (benefit : h+R.ncard+deletionBudget (G.induce W) j≤(I∩W).ncard) :
    h≤savedAt G I j := by
  have sub : I⊆(I\W)∪W := fun x hx => by
    by_cases w : x∈W
    · exact Or.inr w
    · exact Or.inl ⟨hx,w⟩
  have split := protected_budget_comparison G I W (I\W) R j sub boundary
  have inter : I∩W⊆I := Set.inter_subset_left
  have num := Set.ncard_sdiff_add_ncard_of_subset inter
  have eq : I\(I∩W)=I\W := by ext v; simp
  rw [eq] at num
  unfold savedAt
  omega
#print axioms protected_budget_comparison
#print axioms protected_layer_saving
end JSP452Audit.StarHost
