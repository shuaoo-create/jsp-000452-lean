import CanonicalSingletons
namespace JSP452Audit.Padded
open SimpleGraph

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

abbrev Spec.CorePoint (_P : Spec V) (S T : Set V) := ↥((S ∪ T)ᶜ : Set V)
abbrev Spec.coreGraph (S T : Set V) := P.G.induce ((S ∪ T)ᶜ : Set V)
abbrev Spec.CoreComponent (S T : Set V) := (P.coreGraph S T).ConnectedComponent

/-- Original vertex lies in the chosen connected component outside S and T. -/
def Spec.inOriginal {S T : Set V} (C : P.CoreComponent S T) (v : V) : Prop :=
  ∃ h : v ∈ ((S ∪ T)ᶜ : Set V), (⟨v,h⟩ : P.CorePoint S T) ∈ C.supp

omit [Fintype V] [DecidableRel P.G.Adj] in
theorem Spec.notST_of_inOriginal {S T : Set V} {C : P.CoreComponent S T} {v : V}
    (hc : P.inOriginal C v) : v∉S ∧ v∉T := by
  rcases hc with ⟨h,_⟩
  exact ⟨fun hs => h (Or.inl hs),fun ht => h (Or.inr ht)⟩

/-- The complete local blocks over C together with all real T-stubs pointing
    into C. The pool may further join several of these fibers. -/
def Spec.onCore {S T : Set V} (C : P.CoreComponent S T) : P.Vertex → Prop
  | .inl ⟨v,.inl w⟩ => P.inOriginal C v ∨ (v∈T ∧ P.inOriginal C w.val)
  | .inl ⟨v,.inr _⟩ => P.inOriginal C v
  | .inr (.inl (.inl a)) => P.inOriginal C a.1
  | .inr (.inl (.inr a)) => P.inOriginal C a.1
  | .inr (.inr _) => False

def Spec.coreTight {S T : Set V} (C : P.CoreComponent S T) : Prop :=
  ∀ u : P.CorePoint S T, u ∈ C.supp → P.optionalCount u.val = 0

def Spec.coreAnchor {S T : Set V} (u : P.CorePoint S T) : P.CanonVertex S T :=
  P.canonicalPoint (P.extraStub u.val ⟨0,P.padding_pos _⟩) (fun h => u.property (Or.inl h))

def Spec.coreMandatory {S T : Set V} (u : P.CorePoint S T) : P.CanonVertex S T :=
  P.canonicalPoint (P.mandatory ⟨u.val,⟨0,P.mandatoryCount_pos _⟩⟩) (fun h => u.property (Or.inr h))

theorem Spec.onCore_kept {S T : Set V} (dis : Disjoint S T) {C : P.CoreComponent S T}
    {z : P.Vertex} (core : P.onCore C z) : P.keptBy S T z := by
  rcases z with ⟨v,w | i⟩ | ((a | b) | j)
  · rcases core with own | ⟨ht,_⟩
    · exact (P.notST_of_inOriginal own).1
    · exact fun hs => Set.disjoint_left.mp dis hs ht
  · exact (P.notST_of_inOriginal core).1
  · exact (P.notST_of_inOriginal core).2
  · exact (P.notST_of_inOriginal core).2
  · exact core.elim

#print axioms Spec.onCore_kept
end JSP452Audit.Padded
