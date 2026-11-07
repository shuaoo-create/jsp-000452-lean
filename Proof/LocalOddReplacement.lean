import ComponentBudget
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Data.Finite.Sum

namespace JSP452Audit.StarHost
open SimpleGraph

private def sumCompEquiv {X Y : Type*} (G : SimpleGraph X) (H : SimpleGraph Y) :
    (G ⊕g H).ConnectedComponent ≃ G.ConnectedComponent ⊕ H.ConnectedComponent := by
  let tag : X ⊕ Y → G.ConnectedComponent ⊕ H.ConnectedComponent :=
    Sum.elim (fun x => Sum.inl (G.connectedComponentMk x)) (fun y => Sum.inr (H.connectedComponentMk y))
  have step : ∀ a b, (G ⊕g H).Adj a b → tag a = tag b := by
    rintro (x|x) (y|y) h
    · exact congrArg Sum.inl (ConnectedComponent.sound (show G.Adj x y from h).reachable)
    · simp at h
    · simp at h
    · exact congrArg Sum.inr (ConnectedComponent.sound (show H.Adj x y from h).reachable)
  have along {a b : X ⊕ Y} (path : (G ⊕g H).Reachable a b) : tag a = tag b := by
    rw [reachable_iff_reflTransGen] at path
    induction path with
    | refl => rfl
    | tail _ edge ih => exact ih.trans (step _ _ edge)
  let split (c : (G ⊕g H).ConnectedComponent) :=
    c.lift tag (fun _ _ path _ => along path.reachable)
  let l : G ↪g G ⊕g H := Embedding.sumInl
  let r : H ↪g G ⊕g H := Embedding.sumInr
  let join : G.ConnectedComponent ⊕ H.ConnectedComponent → (G ⊕g H).ConnectedComponent :=
    Sum.elim (fun c => c.map l.toHom) (fun c => c.map r.toHom)
  refine ⟨split,join,?_,?_⟩
  · intro c
    refine c.ind ?_
    rintro (x|y) <;> rfl
  · rintro (c|d)
    · exact c.ind (fun _ => rfl)
    · exact d.ind (fun _ => rfl)

theorem odd_ncard_sumGraph {X Y : Type*} [Finite X] [Finite Y]
    (G : SimpleGraph X) (H : SimpleGraph Y) :
    (G ⊕g H).oddComponents.ncard = G.oddComponents.ncard + H.oddComponents.ncard := by
  let e := sumCompEquiv G H
  have mem (z : X ⊕ Y) (c : G.ConnectedComponent ⊕ H.ConnectedComponent) :
      z ∈ (e.symm c).supp ↔
        Sum.elim (fun x => Sum.inl (G.connectedComponentMk x))
          (fun y => Sum.inr (H.connectedComponentMk y)) z = c := by
    change (G ⊕g H).connectedComponentMk z = e.symm c ↔ _
    rw [← e.injective.eq_iff, e.apply_symm_apply]
    cases z <;> rfl
  have l (c : G.ConnectedComponent) : (e.symm (Sum.inl c)).supp = Sum.inl '' c.supp := by
    ext z
    rw [mem]
    cases z with
    | inl x => simp [ConnectedComponent.supp]
    | inr y => simp
  have r (c : H.ConnectedComponent) : (e.symm (Sum.inr c)).supp = Sum.inr '' c.supp := by
    ext z
    rw [mem]
    cases z with
    | inl x => simp
    | inr y => simp [ConnectedComponent.supp]
  let test : G.ConnectedComponent ⊕ H.ConnectedComponent → Prop :=
    Sum.elim (· ∈ G.oddComponents) (· ∈ H.oddComponents)
  have ok (c) : test c ↔ e.symm c ∈ (G ⊕g H).oddComponents := by
    cases c with
    | inl c =>
      change Odd c.supp.ncard ↔ Odd (e.symm (Sum.inl c)).supp.ncard
      rw [l,Set.ncard_image_of_injective _ Sum.inl_injective]
    | inr c =>
      change Odd c.supp.ncard ↔ Odd (e.symm (Sum.inr c)).supp.ncard
      rw [r,Set.ncard_image_of_injective _ Sum.inr_injective]
  let equiv := ((e.symm.subtypeEquiv ok).symm).trans (Equiv.subtypeSum (p := test))
  exact (Nat.card_congr equiv).trans Nat.card_sum

private noncomputable def componentSplit {X : Type*} (Y : SimpleGraph X) (c : Y.ConnectedComponent) :
    (Y.induce c.supp ⊕g Y.induce c.suppᶜ) ≃g Y := by
  classical
  refine ⟨Equiv.Set.sumCompl c.supp,?_⟩
  rintro (a|a) (b|b)
  · rfl
  · change Y.Adj a.val b.val ↔ _
    exact ⟨fun e => (b.property ((c.mem_supp_congr_adj e).mp a.property)).elim,by simp⟩
  · change Y.Adj a.val b.val ↔ _
    exact ⟨fun e => (a.property ((c.mem_supp_congr_adj e).mpr b.property)).elim,by simp⟩
  · rfl

private noncomputable def componentSplitAfter {X : Type*} (Y : SimpleGraph X)
    (c : Y.ConnectedComponent) (Z : Set c.supp) :
    (((Y.induce c.supp).induce Zᶜ) ⊕g Y.induce c.suppᶜ) ≃g
      Y.induce (Subtype.val '' Z)ᶜ := by
  classical
  let U : Set X := Subtype.val '' Z
  let f : ↥(Zᶜ : Set c.supp) ⊕ ↥(c.suppᶜ : Set X) → ↥(Uᶜ : Set X)
    | .inl a => ⟨a.val.val,by
        rintro ⟨b,mem,same⟩
        exact a.property ((Subtype.ext same : b = a.val) ▸ mem)⟩
    | .inr b => ⟨b.val,by rintro ⟨a,_,h⟩; exact b.property (h ▸ a.property)⟩
  have inj : Function.Injective f := by
    rintro (a|a) (b|b) h
    · exact congrArg Sum.inl (Subtype.ext (Subtype.ext (congrArg (fun y : ↥(Uᶜ : Set X) => y.val) h)))
    · have e : a.val.val = b.val := congrArg Subtype.val h
      exact (b.property (e ▸ a.val.property)).elim
    · have e : a.val = b.val.val := congrArg Subtype.val h
      exact (a.property (e.symm ▸ b.val.property)).elim
    · exact congrArg Sum.inr (Subtype.ext (congrArg (fun y : ↥(Uᶜ : Set X) => y.val) h))
  have surj : Function.Surjective f := by
    rintro ⟨x,hx⟩
    by_cases inside : x ∈ c.supp
    · have h : (⟨x,inside⟩ : c.supp) ∉ Z := fun hz => hx ⟨_,hz,rfl⟩
      exact ⟨Sum.inl ⟨⟨x,inside⟩,h⟩,rfl⟩
    · exact ⟨Sum.inr ⟨x,inside⟩,rfl⟩
  refine ⟨Equiv.ofBijective f ⟨inj,surj⟩,?_⟩
  rintro (a|a) (b|b)
  · rfl
  · change Y.Adj a.val.val b.val ↔ _
    exact ⟨fun e => (b.property ((c.mem_supp_congr_adj e).mp a.val.property)).elim,by simp⟩
  · change Y.Adj a.val b.val.val ↔ _
    exact ⟨fun e => (a.property ((c.mem_supp_congr_adj e).mpr b.val.property)).elim,by simp⟩
  · rfl

/-- Replacing one original component by its actual induced remainder affects
the odd-component count by precisely the parity of that original component
and the actual number of surviving odd components inside it. -/
theorem odd_components_replace_component {X : Type*} [Finite X] (Y : SimpleGraph X)
    (c : Y.ConnectedComponent) (Z : Set c.supp) :
    (Y.induce (Subtype.val '' Z)ᶜ).oddComponents.ncard +
      (if Odd (Nat.card c.supp) then 1 else 0) =
    Y.oddComponents.ncard + ((Y.induce c.supp).induce Zᶜ).oddComponents.ncard := by
  classical
  let Q := Y.induce c.supp
  have connected : Q.Connected := c.connected_toSimpleGraph
  let _ : Subsingleton Q.ConnectedComponent := connected.preconnected.subsingleton_connectedComponent
  have bound : Q.oddComponents.ncard ≤ 1 :=
    (Set.ncard_le_one (s := Q.oddComponents) (Set.toFinite _)).mpr (fun _ _ _ _ => Subsingleton.elim _ _)
  have parity := odd_ncard_oddComponents Q
  have own : Q.oddComponents.ncard = if Odd (Nat.card c.supp) then 1 else 0 := by
    split
    · next h => have ord := Nat.odd_iff.mp (parity.mpr h); omega
    · next h => have ord := mt parity.mp h; rw [Nat.odd_iff] at ord; omega
  have before := odd_ncard_iso (componentSplit Y c)
  have after := odd_ncard_iso (componentSplitAfter Y c Z)
  rw [odd_ncard_sumGraph] at before after
  change Q.oddComponents.ncard + _ = _ at before
  omega

#print axioms odd_ncard_sumGraph
#print axioms odd_components_replace_component
end JSP452Audit.StarHost
