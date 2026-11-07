import Mathlib.Combinatorics.SimpleGraph.Tutte

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*}

/-- Original vertex label of a point in an actual component outside the cut. -/
def cutBlockVertex (G : SimpleGraph X) (S : Set X)
    (c : (G.induce Sᶜ).ConnectedComponent) : c.supp ↪ X where
  toFun a := a.1.1
  inj' := by intro a b e; exact Subtype.ext (Subtype.ext e)

theorem cutBlockVertex_outside (G : SimpleGraph X) (S : Set X)
    (c : (G.induce Sᶜ).ConnectedComponent) (a : c.supp) :
    cutBlockVertex G S c a ∉ S := a.1.property

abbrev CutBlockColors (G : SimpleGraph X) (S : Set X) :=
  (c : (G.induce Sᶜ).ConnectedComponent) → SimpleGraph c.supp

/-- Edges that touch a red control have priority. Other red edges are precisely
the images of the given local red edges. Every colored edge is an actual host edge. -/
def barrierRed (G : SimpleGraph X) (S A : Set X) (r : CutBlockColors G S) : SimpleGraph X where
  Adj x y := G.Adj x y ∧ (x ∈ A ∨ y ∈ A ∨
    ∃ (c : (G.induce Sᶜ).ConnectedComponent) (a b : c.supp),
      cutBlockVertex G S c a = x ∧ cutBlockVertex G S c b = y ∧ (r c).Adj a b)
  symm := ⟨by
    rintro x y ⟨host, hx | hy | ⟨c,a,b,hx,hy,edge⟩⟩
    · exact ⟨host.symm,Or.inr (Or.inl hx)⟩
    · exact ⟨host.symm,Or.inl hy⟩
    · exact ⟨host.symm,Or.inr (Or.inr ⟨c,b,a,hy,hx,edge.symm⟩)⟩⟩
  loopless := ⟨fun _ e => e.1.ne rfl⟩

theorem barrierRed_le (G : SimpleGraph X) (S A : Set X) (r : CutBlockColors G S) :
    barrierRed G S A r ≤ G := fun _ _ h => h.1

theorem barrierRed_at_cut (G : SimpleGraph X) (S A : Set X) (r : CutBlockColors G S)
    {x y : X} (touch : x ∈ S ∨ y ∈ S) :
    (barrierRed G S A r).Adj x y ↔ G.Adj x y ∧ (x ∈ A ∨ y ∈ A) := by
  constructor
  · rintro ⟨host, redX | redY | ⟨c,a,b,rfl,rfl,_⟩⟩
    · exact ⟨host,Or.inl redX⟩
    · exact ⟨host,Or.inr redY⟩
    · exact False.elim (touch.elim (cutBlockVertex_outside G S c a) (cutBlockVertex_outside G S c b))
  · rintro ⟨host,hx|hy⟩
    · exact ⟨host,Or.inl hx⟩
    · exact ⟨host,Or.inr (Or.inl hy)⟩

theorem barrierBlue_at_cut (G : SimpleGraph X) (S A : Set X) (r : CutBlockColors G S)
    {x y : X} (touch : x ∈ S ∨ y ∈ S) :
    (G \ barrierRed G S A r).Adj x y ↔ G.Adj x y ∧ x ∉ A ∧ y ∉ A := by
  change G.Adj x y ∧ ¬ (barrierRed G S A r).Adj x y ↔ _
  rw [barrierRed_at_cut G S A r touch]
  tauto

theorem barrierBlue_uses_control (G : SimpleGraph X) (S A : Set X) (r : CutBlockColors G S)
    {x y : X} (touch : x ∈ S ∨ y ∈ S) (h : (G \ barrierRed G S A r).Adj x y) :
    x ∈ S \ A ∨ y ∈ S \ A := by
  have no := ((barrierBlue_at_cut G S A r touch).mp h).2
  exact touch.elim (fun hx => Or.inl ⟨hx,no.1⟩) (fun hy => Or.inr ⟨hy,no.2⟩)

theorem barrierRed_in_block (G : SimpleGraph X) (S A : Set X) (hAS : A ⊆ S)
    (r : CutBlockColors G S) (hr : ∀ c, r c ≤ (G.induce Sᶜ).induce c.supp)
    (c : (G.induce Sᶜ).ConnectedComponent) (a b : c.supp) :
    (barrierRed G S A r).Adj (cutBlockVertex G S c a) (cutBlockVertex G S c b) ↔
      (r c).Adj a b := by
  constructor
  · rintro ⟨_,hx | hy | ⟨d,u,v,hu,hv,edge⟩⟩
    · exact False.elim (cutBlockVertex_outside G S c a (hAS hx))
    · exact False.elim (cutBlockVertex_outside G S c b (hAS hy))
    · have eu : u.val = a.val := Subtype.ext hu
      have same : d = c := u.property.symm.trans
        ((congrArg (G.induce Sᶜ).connectedComponentMk eu).trans a.property)
      subst d
      have su : u = a := Subtype.ext eu
      have sv : v = b := (cutBlockVertex G S c).injective hv
      simpa only [su,sv] using edge
  · intro edge
    exact ⟨hr c edge,Or.inr (Or.inr ⟨c,a,b,rfl,rfl,edge⟩)⟩

theorem barrierBlue_in_block (G : SimpleGraph X) (S A : Set X) (hAS : A ⊆ S)
    (r : CutBlockColors G S) (hr : ∀ c, r c ≤ (G.induce Sᶜ).induce c.supp)
    (c : (G.induce Sᶜ).ConnectedComponent) (a b : c.supp) :
    (G \ barrierRed G S A r).Adj (cutBlockVertex G S c a) (cutBlockVertex G S c b) ↔
      ((G.induce Sᶜ).induce c.supp \ r c).Adj a b := by
  change _ ∧ ¬ (barrierRed G S A r).Adj _ _ ↔ _ ∧ ¬ (r c).Adj a b
  rw [barrierRed_in_block G S A hAS r hr c a b]
  rfl

#print axioms barrierRed_le
#print axioms barrierRed_at_cut
#print axioms barrierBlue_uses_control
#print axioms barrierRed_in_block
#print axioms barrierBlue_in_block
end JSP452Audit.StarHost
