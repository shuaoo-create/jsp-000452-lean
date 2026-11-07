import CanonicalCut

namespace JSP452Audit.Padded
open SimpleGraph

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

abbrev Spec.CanonVertex (S T : Set V) := ↥(P.canonicalKept S T : Set P.Vertex)

noncomputable abbrev Spec.canonGraph (S T : Set V) : SimpleGraph (P.CanonVertex S T) :=
  P.graph.induce (P.canonicalKept S T : Set P.Vertex)

def Spec.canonicalPoint {S T : Set V} (z : P.Vertex) (h : P.keptBy S T z) :
    P.CanonVertex S T := ⟨z,(P.mem_canonicalKept S T z).2 h⟩

/-- Exactly the three specified families, indexed by the original auxiliary labels. -/
def Spec.singletonLabel (S T : Set V) : P.Vertex → Prop
  | .inl ⟨v,.inl w⟩ => v ∈ T ∧ w.val ∈ S
  | .inl ⟨v,.inr _⟩ => v ∈ T
  | .inr (.inl (.inl a)) => a.1 ∈ S
  | _ => False

theorem Spec.singletonLabel_kept {S T : Set V} (dis : Disjoint S T) {z : P.Vertex}
    (h : P.singletonLabel S T z) : P.keptBy S T z := by
  rcases z with ⟨v,w | i⟩ | ((a | o) | g)
  · exact fun hs => Set.disjoint_left.mp dis hs h.1
  · exact fun hs => Set.disjoint_left.mp dis hs h
  · exact Set.disjoint_left.mp dis h
  · exact h.elim
  · exact h.elim

private theorem token_excluded {S T : Set V} {t : P.Token} {v : V} (ht : v ∈ T)
    (own : P.ownedAt t v) : ¬ P.keptBy S T (.inr t) := by
  rcases t with (a | b) | g
  · exact fun kept => kept (own ▸ ht)
  · exact fun kept => kept (own ▸ ht)
  · exact own.elim

/-- The only possible retained neighbor of a real stub based in T is its opposite stub. -/
theorem Spec.canonical_real_neighbor {S T : Set V} {v w : V} (edge : P.G.Adj v w)
    (ht : v ∈ T) (y : P.CanonVertex S T) (adj : P.graph.Adj (P.realStub v w edge) y.val) :
    y.val = P.realStub w v edge.symm := by
  obtain ⟨s | t,kept⟩ := y
  · have e : P.cross ⟨v,.inl ⟨w,edge⟩⟩ ⟨w,.inl ⟨v,edge.symm⟩⟩ := ⟨rfl,rfl⟩
    exact congrArg Sum.inl (P.cross_partner_unique adj e)
  · exact (token_excluded P ht adj ((P.mem_canonicalKept S T _).1 kept)).elim

theorem Spec.canonical_singleton_isolated {S T : Set V} (dis : Disjoint S T) {z : P.Vertex}
    (hz : P.singletonLabel S T z) (y : P.CanonVertex S T) :
    ¬ (P.canonGraph S T).Adj (P.canonicalPoint z (P.singletonLabel_kept dis hz)) y := by
  intro adj
  have hy := (P.mem_canonicalKept S T y.val).1 y.property
  rcases z with ⟨v,w | i⟩ | ((a | o) | g)
  · have he := P.canonical_real_neighbor w.property hz.1 y adj
    rw [he] at hy
    exact hy hz.2
  · rcases y with ⟨s | t,kept⟩
    · exact adj.elim
    · exact token_excluded P hz adj hy
  · rcases y with ⟨s | t,kept⟩
    · have eq : a.1 = s.1 := adj
      exact hy (eq ▸ hz)
    · exact adj.1.elim
  · exact hz.elim
  · exact hz.elim

private theorem support_closed {X : Type*} {H : SimpleGraph X} (x : X) {s : Set X}
    (hx : x ∈ s) (closed : ∀ ⦃a b⦄, a ∈ s → H.Adj a b → b ∈ s) :
    (H.connectedComponentMk x).supp ⊆ s := by
  intro y hy
  have hr : H.Reachable x y := ConnectedComponent.exact (show H.connectedComponentMk y = _ from hy).symm
  rw [reachable_iff_reflTransGen] at hr
  clear hy
  induction hr with
  | refl => exact hx
  | tail _ adj ih => exact closed ih adj

theorem Spec.canonical_singleton_support {S T : Set V} (dis : Disjoint S T) {z : P.Vertex}
    (hz : P.singletonLabel S T z) :
    let pt := P.canonicalPoint z (P.singletonLabel_kept dis hz)
    ((P.canonGraph S T).connectedComponentMk pt).supp = {pt} := by
  intro pt
  apply Set.Subset.antisymm
  · apply support_closed pt (Set.mem_singleton _)
    intro x y hx adj
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact (P.canonical_singleton_isolated dis hz y adj).elim
  · exact Set.singleton_subset_iff.mpr rfl

/-- Distinct singleton labels give distinct odd components. -/
noncomputable def Spec.canonicalSingletonEmbedding {S T : Set V} (dis : Disjoint S T) :
    {z : P.Vertex // P.singletonLabel S T z} ↪ (P.canonGraph S T).oddComponents where
  toFun z := ⟨(P.canonGraph S T).connectedComponentMk
    (P.canonicalPoint z.val (P.singletonLabel_kept dis z.property)),by
      change Odd ((P.canonGraph S T).connectedComponentMk _).supp.ncard
      rw [P.canonical_singleton_support dis z.property,Set.ncard_singleton]
      decide⟩
  inj' := by
    intro a b h
    have eq := congrArg (fun c : (P.canonGraph S T).oddComponents => c.val.supp) h
    change ((P.canonGraph S T).connectedComponentMk _).supp =
      ((P.canonGraph S T).connectedComponentMk _).supp at eq
    rw [P.canonical_singleton_support dis a.property, P.canonical_singleton_support dis b.property] at eq
    have same : P.canonicalPoint a.val (P.singletonLabel_kept dis a.property) =
        P.canonicalPoint b.val (P.singletonLabel_kept dis b.property) := by simpa using eq
    exact Subtype.ext (congrArg (fun x : P.CanonVertex S T => x.val) same)


/-- Index decomposition without overlap: S-mandatory, T-padding, and T-to-S incidences. -/
abbrev Spec.SingletonIndex (S T : Set V) :=
  ((v : S) × Fin (P.mandatoryCount v.val)) ⊕
  (((v : T) × Fin (P.padding v.val)) ⊕
    ((v : T) × {w : P.G.neighborSet v.val // w.val ∈ S}))

def Spec.singletonIndexEquiv (S T : Set V) :
    P.SingletonIndex S T ≃ {z : P.Vertex // P.singletonLabel S T z} where
  toFun
    | .inl ⟨v,i⟩ => ⟨P.mandatory ⟨v.val,i⟩,v.property⟩
    | .inr (.inl ⟨v,i⟩) => ⟨P.extraStub v.val i,v.property⟩
    | .inr (.inr ⟨v,w⟩) => ⟨P.realStub v.val w.val.val w.val.property,v.property,w.property⟩
  invFun
    | ⟨.inl ⟨v,.inl w⟩,hv⟩ => .inr (.inr ⟨⟨v,hv.1⟩,⟨w,hv.2⟩⟩)
    | ⟨.inl ⟨v,.inr i⟩,hv⟩ => .inr (.inl ⟨⟨v,hv⟩,i⟩)
    | ⟨.inr (.inl (.inl a)),ha⟩ => .inl ⟨⟨a.1,ha⟩,a.2⟩
    | ⟨.inr (.inl (.inr _)),h⟩ => h.elim
    | ⟨.inr (.inr _),h⟩ => h.elim
  left_inv := by rintro (⟨v,i⟩|⟨v,i⟩|⟨v,w⟩) <;> rfl
  right_inv := by
    rintro ⟨⟨v,w|i⟩|((a|b)|g),h⟩ <;> first | rfl | exact h.elim

theorem Spec.singletonIndex_count (S T : Set V) [Fintype S] [Fintype T] :
    Nat.card (P.SingletonIndex S T) =
      (∑ v : S, P.mandatoryCount v.val) + (∑ v : T, P.padding v.val) +
        (∑ v : T, Nat.card {w : P.G.neighborSet v.val // w.val ∈ S}) := by
  classical
  simp only [Spec.SingletonIndex,Nat.card_sum,Nat.card_sigma,Nat.card_fin,Nat.add_assoc]

theorem Spec.singletonIndex_le_odd {S T : Set V} (dis : Disjoint S T) :
    Nat.card (P.SingletonIndex S T) ≤ (P.canonGraph S T).oddComponents.ncard := by
  exact Nat.card_le_card_of_injective _
    ((P.singletonIndexEquiv S T).toEmbedding.trans (P.canonicalSingletonEmbedding dis)).injective

/-- The kept end of any edge with its base vertex in T. -/
def Spec.canonicalTStub {S T : Set V} (dis : Disjoint S T) {v w : V} (hv : v ∈ T)
    (edge : P.G.Adj v w) : P.CanonVertex S T :=
  P.canonicalPoint (P.realStub v w edge) (fun hs => Set.disjoint_left.mp dis hs hv)

/-- Both endpoints at T survive and form their entire two-vertex component. -/
theorem Spec.canonical_TT_support {S T : Set V} (dis : Disjoint S T) {v w : V}
    (hv : v ∈ T) (hw : w ∈ T) (edge : P.G.Adj v w) :
    let x := P.canonicalTStub dis hv edge
    let y := P.canonicalTStub dis hw edge.symm
    ((P.canonGraph S T).connectedComponentMk x).supp = {x,y} := by
  intro x y
  have xy : (P.canonGraph S T).Adj x y := ⟨rfl,rfl⟩
  apply Set.Subset.antisymm
  · apply support_closed x (Set.mem_insert _ _)
    intro a b ha ab
    rcases Set.mem_insert_iff.mp ha with rfl | hy
    · have eq : b = y := Subtype.ext (P.canonical_real_neighbor edge hv b ab)
      exact Or.inr (Set.mem_singleton_iff.mpr eq)
    · obtain rfl := Set.mem_singleton_iff.mp hy
      have eq : b = x := Subtype.ext (P.canonical_real_neighbor edge.symm hw b ab)
      exact Or.inl eq
  · intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz'
    · rfl
    · obtain rfl := Set.mem_singleton_iff.mp hz'
      exact ConnectedComponent.sound xy.symm.reachable

theorem Spec.canonical_TT_ncard {S T : Set V} (dis : Disjoint S T) {v w : V}
    (hv : v ∈ T) (hw : w ∈ T) (edge : P.G.Adj v w) :
    ((P.canonGraph S T).connectedComponentMk (P.canonicalTStub dis hv edge)).supp.ncard = 2 := by
  rw [P.canonical_TT_support dis hv hw edge]
  have adj : (P.canonGraph S T).Adj (P.canonicalTStub dis hv edge)
      (P.canonicalTStub dis hw edge.symm) := ⟨rfl,rfl⟩
  simp [adj.ne]

#print axioms Spec.singletonIndexEquiv
#print axioms Spec.singletonIndex_count
#print axioms Spec.singletonIndex_le_odd
#print axioms Spec.canonical_TT_support
#print axioms Spec.canonical_TT_ncard

#print axioms Spec.canonicalSingletonEmbedding
end JSP452Audit.Padded
