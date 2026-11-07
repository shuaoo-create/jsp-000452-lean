import Mathlib.Combinatorics.SimpleGraph.Finite

/- The auxiliary graph in §1 of the factor-from-Tutte reduction. This file
   defines its vertices and edges; no matching or deficiency assertion is used. -/
namespace JSP452Audit.Padded

structure Spec (V : Type*) where
  G : SimpleGraph V
  A : V → ℕ
  B : V → ℕ
  extra : Bool

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

def Spec.padding (v : V) : ℕ := 1 + (P.A v - P.G.degree v)
def Spec.mandatoryCount (v : V) : ℕ := P.G.degree v + P.padding v - P.A v
def Spec.optionalCount (v : V) : ℕ := P.A v + P.B v - P.G.degree v

/-- Every local block has a dummy stub and a mandatory token, even at
    isolated vertices or when the red cap exceeds the degree. -/
theorem Spec.padding_pos (v : V) : 0 < P.padding v := by
  unfold Spec.padding
  omega

theorem Spec.mandatoryCount_pos (v : V) : 0 < P.mandatoryCount v := by
  unfold Spec.mandatoryCount Spec.padding
  omega

/-- A real stub contains a neighbor and its incidence proof. -/
abbrev Spec.Stub := (v : V) × (P.G.neighborSet v ⊕ Fin (P.padding v))
abbrev Spec.Mandatory := (v : V) × Fin (P.mandatoryCount v)
abbrev Spec.Optional := (v : V) × Fin (P.optionalCount v)
abbrev Spec.Token := (P.Mandatory ⊕ P.Optional) ⊕ Fin (if P.extra then 1 else 0)
abbrev Spec.Vertex := P.Stub ⊕ P.Token

def Spec.realStub (v w : V) (h : P.G.Adj v w) : P.Vertex :=
  .inl ⟨v, .inl ⟨w, h⟩⟩

def Spec.extraStub (v : V) (i : Fin (P.padding v)) : P.Vertex :=
  .inl ⟨v, .inr i⟩

def Spec.mandatory (a : P.Mandatory) : P.Vertex := .inr (.inl (.inl a))
def Spec.optional (a : P.Optional) : P.Vertex := .inr (.inl (.inr a))
def Spec.globalToken (i : Fin (if P.extra then 1 else 0)) : P.Vertex := .inr (.inr i)

def Spec.cross : P.Stub → P.Stub → Prop
  | ⟨v, .inl w⟩, ⟨u, .inl z⟩ => v = z.val ∧ u = w.val
  | _, _ => False

/-- The global token has no local owner. -/
def Spec.ownedAt : P.Token → V → Prop
  | .inl (.inl a), v => a.1 = v
  | .inl (.inr a), v => a.1 = v
  | .inr _, _ => False

def Spec.inPool : P.Token → Prop
  | .inl (.inl _) => False
  | .inl (.inr _) => True
  | .inr _ => True

def Spec.link : P.Vertex → P.Vertex → Prop
  | .inl s, .inl r => P.cross s r
  | .inl s, .inr t | .inr t, .inl s => P.ownedAt t s.1
  | .inr t, .inr u => P.inPool t ∧ P.inPool u ∧ t ≠ u

private theorem cross_symm (s r : P.Stub) (h : P.cross s r) : P.cross r s := by
  obtain ⟨v, sw | si⟩ := s <;> obtain ⟨u, rz | ri⟩ := r
  · exact ⟨h.2, h.1⟩
  all_goals exact h.elim

private theorem cross_irrefl (s : P.Stub) : ¬ P.cross s s := by
  obtain ⟨v, w | i⟩ := s
  · intro h
    exact P.G.ne_of_adj w.property h.1
  · intro h
    exact h.elim

theorem Spec.link_symm (x y : P.Vertex) (h : P.link x y) : P.link y x := by
  cases x with
  | inl s =>
    cases y with
    | inl r => exact cross_symm P s r h
    | inr _ => exact h
  | inr t =>
    cases y with
    | inl _ => exact h
    | inr u => exact ⟨h.2.1, h.1, Ne.symm h.2.2⟩

theorem Spec.link_irrefl (x : P.Vertex) : ¬ P.link x x := by
  cases x with
  | inl s => exact cross_irrefl P s
  | inr t => exact fun h => h.2.2 rfl

def Spec.graph : SimpleGraph P.Vertex where
  Adj := P.link
  symm := ⟨P.link_symm⟩
  loopless := ⟨P.link_irrefl⟩

/-- The two real stubs are adjacent exactly when they represent opposite
    orientations of the same original edge. -/
theorem Spec.real_adj_real_iff {v w u z : V} (h : P.G.Adj v w) (k : P.G.Adj u z) :
    P.graph.Adj (P.realStub v w h) (P.realStub u z k) ↔ v = z ∧ u = w := Iff.rfl

theorem Spec.optional_adj_optional_iff (a b : P.Optional) :
    P.graph.Adj (P.optional a) (P.optional b) ↔ a ≠ b := by
  simp [Spec.graph, Spec.link, Spec.optional, Spec.inPool]

theorem Spec.optional_adj_global (a : P.Optional) (i : Fin (if P.extra then 1 else 0)) :
    P.graph.Adj (P.optional a) (P.globalToken i) := by
  simp [Spec.graph, Spec.link, Spec.optional, Spec.globalToken, Spec.inPool]

theorem Spec.stub_adj_mandatory_iff (s : P.Stub) (a : P.Mandatory) :
    P.graph.Adj (.inl s) (P.mandatory a) ↔ a.1 = s.1 := Iff.rfl

theorem Spec.stub_adj_optional_iff (s : P.Stub) (a : P.Optional) :
    P.graph.Adj (.inl s) (P.optional a) ↔ a.1 = s.1 := Iff.rfl

theorem Spec.not_stub_adj_global (s : P.Stub) (i : Fin (if P.extra then 1 else 0)) :
    ¬ P.graph.Adj (.inl s) (P.globalToken i) := fun h => h.elim

noncomputable abbrev Spec.vertexFintype : Fintype P.Vertex := inferInstance

#print axioms Spec.padding_pos
#print axioms Spec.mandatoryCount_pos
#print axioms Spec.link_symm
#print axioms Spec.link_irrefl
#print axioms Spec.graph
#print axioms Spec.real_adj_real_iff
#print axioms Spec.optional_adj_optional_iff
#print axioms Spec.optional_adj_global
#print axioms Spec.stub_adj_mandatory_iff
#print axioms Spec.stub_adj_optional_iff
#print axioms Spec.not_stub_adj_global
#print axioms Spec.vertexFintype

end JSP452Audit.Padded
