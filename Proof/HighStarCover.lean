import SelectCenter

namespace JSP452Audit.StarHost
open SimpleGraph
variable {I X : Type*} [Fintype I] [Finite X]

/-- The distinguished center of this particular star copy sees all its distinct leaves. -/
theorem star_copy_center_degree (C : SimpleGraph X) {j : ℕ} (f : (oneStar j).Copy C) :
    j ≤ Nat.card (C.neighborSet (f (center (fun _ : Fin 1 => j) 0))) := by
  let n := fun _ : Fin 1 => j
  let v := f (center n 0)
  let nbr (l : Fin j) : C.neighborSet v := ⟨f (leaf n ⟨0,l⟩),f.toHom.map_adj (starEdge n ⟨0,l⟩)⟩
  have inj : Function.Injective nbr := by
    intro a b h
    have he := f.injective (congrArg (fun w : C.neighborSet v => w.val) h)
    exact Fin.ext (Nat.succ.inj (congrArg (fun z : Vertices n => z.2.val) he))
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective nbr inj

private def smallStarMap {n : I → ℕ} (i : I) (j : ℕ) (le : j ≤ n i) :
    Vertices (fun _ : Fin 1 => j) → Vertices n :=
  fun u => ⟨i,⟨u.2.val,by exact Nat.lt_of_lt_of_le u.2.isLt (Nat.succ_le_succ le)⟩⟩

omit [Fintype I] in
private theorem smallStarMap_injective {n : I → ℕ} (i : I) (j : ℕ) (le : j ≤ n i) :
    Function.Injective (smallStarMap i j le) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ eq
  obtain rfl : a=b := Subsingleton.elim _ _
  have v := congrArg (fun z : Vertices n => z.2.val) eq
  exact congrArg (Sigma.mk a) (Fin.ext v)

private def smallStarCopy {n : I → ℕ} (i : I) (j : ℕ) (le : j ≤ n i) :
    (oneStar j).Copy (forest n) where
  toHom := {
    toFun := smallStarMap i j le
    map_rel' := by
      rintro x y ⟨diff,h | h⟩
      · exact ⟨fun e => diff (smallStarMap_injective i j le e),Or.inl ⟨rfl,h.2⟩⟩
      · exact ⟨fun e => diff (smallStarMap_injective i j le e),Or.inr ⟨rfl,h.2⟩⟩ }
  injective' := smallStarMap_injective i j le

/-- Every qualifying component contains a threshold-sized star on its original
labels. One covered image per component gives an injection into A. -/
theorem count_large_of_hits (C : SimpleGraph X) (A : Set X) (p : ℕ) (n : I → ℕ)
    (hits : ∀ f : (oneStar (p+1)).Copy C, ∃ x, f x ∈ A)
    (copy : (forest n).IsContained C) :
    (Finset.univ.filter (fun i => p+1 ≤ n i)).card ≤ A.ncard := by
  classical
  obtain ⟨f⟩ := copy
  let W := Finset.univ.filter (fun i => p+1 ≤ n i)
  have wide (w : W) : p+1 ≤ n w.val := (Finset.mem_filter.mp w.property).2
  let sub (w : W) := smallStarCopy w.val (p+1) (wide w)
  have meet (w : W) : ∃ x, f (sub w x) ∈ A := hits (f.comp (sub w))
  let pick (w : W) : A := ⟨f (sub w (meet w).choose),(meet w).choose_spec⟩
  have inj : Function.Injective pick := by
    intro u w h
    exact Subtype.ext (congrArg Sigma.fst (f.injective (congrArg (fun x : A => x.val) h)))
  have bound := Nat.card_le_card_of_injective pick inj
  change W.card ≤ Nat.card A
  rwa [Nat.card_eq_fintype_card (α := ↥W),Fintype.card_coe] at bound

/-- A degree bound after deleting A forces each threshold star to meet A. -/
theorem count_large_of_degree_cut (C : SimpleGraph X) (A : Set X) (p : ℕ) (n : I → ℕ)
    (cap : ∀ x : ↥(Aᶜ : Set X), Nat.card ((C.induce Aᶜ).neighborSet x) ≤ p)
    (copy : (forest n).IsContained C) :
    (Finset.univ.filter (fun i => p+1 ≤ n i)).card ≤ A.ncard := by
  apply count_large_of_hits C A p n _ copy
  intro f
  by_contra! none
  let lift : (oneStar (p+1)).Copy (C.induce Aᶜ) :=
    {toHom := {toFun := fun x => ⟨f x,none x⟩, map_rel' := fun h => f.toHom.map_adj h}
     injective' := fun _ _ eq => f.injective (congrArg Subtype.val eq)}
  have deg := star_copy_center_degree (C.induce Aᶜ) lift
  have tooSmall := cap (lift (center (fun _ : Fin 1 => p+1) 0))
  omega

/-- Redrawing edges incident to A leaves the rest under the old bounded coloring. -/
theorem count_large_of_edge_cover (C F : SimpleGraph X) (A : Set X) (p : ℕ) (n : I → ℕ)
    (edges : ∀ ⦃x y⦄, C.Adj x y → x ∈ A ∨ y ∈ A ∨ F.Adj x y)
    (cap : ∀ x, Nat.card (F.neighborSet x) ≤ p) (copy : (forest n).IsContained C) :
    (Finset.univ.filter (fun i => p+1 ≤ n i)).card ≤ A.ncard := by
  apply count_large_of_degree_cut C A p n _ copy
  intro x
  let away := C.induce Aᶜ
  let incl (y : away.neighborSet x) : F.neighborSet x.val := ⟨y.val.val,
    (edges y.property).resolve_left x.property |>.resolve_left y.val.property⟩
  have inj : Function.Injective incl := fun _ _ eq =>
    Subtype.ext (Subtype.ext (congrArg (fun y : F.neighborSet x.val => y.val) eq))
  exact (Nat.card_le_card_of_injective incl inj).trans (cap x.val)

/-- If every vertex of degree above q is covered, use each large star's own center. -/
theorem count_large_of_center_cover (C : SimpleGraph X) (B : Set X) (q : ℕ) (n : I → ℕ)
    (centers : ∀ x, q < Nat.card (C.neighborSet x) → x ∈ B) (copy : (forest n).IsContained C) :
    (Finset.univ.filter (fun i => q+1 ≤ n i)).card ≤ B.ncard := by
  apply count_large_of_hits C B q n _ copy
  intro f
  exact ⟨_,centers _ (star_copy_center_degree C f)⟩

#print axioms count_large_of_hits
#print axioms count_large_of_degree_cut
#print axioms count_large_of_edge_cover
#print axioms count_large_of_center_cover
end JSP452Audit.StarHost
