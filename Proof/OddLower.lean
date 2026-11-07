import CoreIdentity
import Mathlib.Data.Finite.Sum

namespace JSP452Audit.Padded
open SimpleGraph
variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj] {S T : Set V}

/-- A tight component is recoverable from its actual canonical component: the
dummy stub at its representative comes from an identifiable original vertex. -/
theorem Spec.same_core_of_tight_cc {C D : P.CoreComponent S T} (tightD : P.coreTight D)
    (same : P.coreCC C = P.coreCC D) : C = D := by
  have inside : P.coreRep C ∈ (P.coreCC D).supp := by rw [← same]; rfl
  obtain ⟨_,memD⟩ := (P.tight_core_mem tightD _).mp inside
  have first : (P.coreGraph S T).connectedComponentMk C.nonempty_supp.choose = C :=
    C.nonempty_supp.choose_spec
  have second : (P.coreGraph S T).connectedComponentMk C.nonempty_supp.choose = D := memD
  exact first.symm.trans second

noncomputable def Spec.tightOddEmbedding (dis : Disjoint S T) :
    ↥(P.tightOdd S T) ↪ (P.canonGraph S T).oddComponents where
  toFun C := ⟨P.coreCC C.val,by
    change Odd (P.coreCC C.val).supp.ncard
    change Odd (Nat.card (P.coreCC C.val).supp)
    rw [Nat.card_congr (P.tightFiberEquiv dis C.property.1)]
    exact C.property.2⟩
  inj' := by
    intro C D same
    exact Subtype.ext (P.same_core_of_tight_cc D.property.1 (congrArg Subtype.val same))

private theorem singleton_ne_core (dis : Disjoint S T) (a : {z // P.singletonLabel S T z})
    (C : P.CoreComponent S T) : (P.canonicalSingletonEmbedding dis a).val ≠ P.coreCC C := by
  intro same
  have mem : P.coreRep C ∈ ((P.canonicalSingletonEmbedding dis a).val).supp := by rw [same]; rfl
  change P.coreRep C ∈ ((P.canonGraph S T).connectedComponentMk
    (P.canonicalPoint a.val (P.singletonLabel_kept dis a.property))).supp at mem
  rw [P.canonical_singleton_support dis a.property] at mem
  have eq := congrArg (fun x : P.CanonVertex S T => x.val) (Set.mem_singleton_iff.mp mem)
  have single : P.singletonLabel S T (P.coreRep C).val := eq.symm ▸ a.property
  exact C.nonempty_supp.choose.property (Or.inr single)

/-- Lower-count witnesses as an injection of a disjoint sum of real labels. -/
noncomputable def Spec.oddLowerEmbedding (dis : Disjoint S T) :
    (P.SingletonIndex S T ⊕ ↥(P.tightOdd S T)) ↪ (P.canonGraph S T).oddComponents where
  toFun := Sum.elim (fun i => P.canonicalSingletonEmbedding dis (P.singletonIndexEquiv S T i))
    (P.tightOddEmbedding dis)
  inj' := by
    rintro (i | C) (j | D) eq
    · exact congrArg Sum.inl ((P.singletonIndexEquiv S T).injective
        ((P.canonicalSingletonEmbedding dis).injective eq))
    · exact (singleton_ne_core P dis (P.singletonIndexEquiv S T i) D.val (congrArg Subtype.val eq)).elim
    · exact (singleton_ne_core P dis (P.singletonIndexEquiv S T j) C.val (congrArg Subtype.val eq.symm)).elim
    · exact congrArg Sum.inr ((P.tightOddEmbedding dis).injective eq)

theorem Spec.singleton_tightOdd_le_odd (dis : Disjoint S T) :
    Nat.card (P.SingletonIndex S T) + (P.tightOdd S T).ncard ≤
      (P.canonGraph S T).oddComponents.ncard := by
  have bound := Nat.card_le_card_of_injective _ (P.oddLowerEmbedding dis).injective
  simpa only [Nat.card_sum, Nat.card_coe_set_eq] using bound

#print axioms Spec.oddLowerEmbedding
#print axioms Spec.singleton_tightOdd_le_odd
end JSP452Audit.Padded
