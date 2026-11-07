import MatchedDeletion

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ)
abbrev Layer (D : ℕ) := Fin D → Bool

private def flipBit {D : ℕ} (f : Layer D) (i : ℕ) : Layer D :=
  fun j => if j.val = i then !(f j) else f j

private theorem flip_twice {D : ℕ} (f : Layer D) (i : ℕ) : flipBit (flipBit f i) i = f := by
  funext j
  by_cases eq : j.val = i <;> simp [flipBit, eq]

private theorem self_ne_flip {D : ℕ} (f : Layer D) {i : ℕ} (hi : i < D) : f ≠ flipBit f i := by
  intro h
  have atI := congrFun h (⟨i,hi⟩ : Fin D)
  simp [flipBit] at atI

private theorem flip_inj {D : ℕ} (f : Layer D) {i j : ℕ} (hi : i < D)
    (h : flipBit f i = flipBit f j) : i = j := by
  by_contra ne
  have atI := congrFun h (⟨i,hi⟩ : Fin D)
  simp [flipBit, ne] at atI

/-- Fill every missing neighbor slot along its own Boolean coordinate. No parallel edges
or loops are introduced, even if the original vertex is isolated. -/
def regularEnvelope : SimpleGraph (X × Layer D) where
  Adj a b := (G.Adj a.1 b.1 ∧ a.2 = b.2) ∨
    (a.1 = b.1 ∧ ∃ i : Fin (D - Nat.card (G.neighborSet a.1)), b.2 = flipBit a.2 i.val)
  symm := ⟨by
    rintro ⟨u,f⟩ ⟨v,g⟩ (⟨h,e⟩ | ⟨uv,i,eq⟩)
    · exact Or.inl ⟨h.symm,e.symm⟩
    · change u = v at uv
      subst v
      exact Or.inr ⟨rfl,i,eq ▸ (flip_twice f i.val).symm⟩⟩
  loopless := ⟨by
    rintro ⟨v,f⟩ (⟨adj,_⟩ | ⟨_,i,h⟩)
    · exact G.irrefl adj
    · exact self_ne_flip f (lt_of_lt_of_le i.isLt (Nat.sub_le _ _)) h⟩

private def envelopeNeighbor (v : X) (f : Layer D) :
    (G.neighborSet v ⊕ Fin (D - Nat.card (G.neighborSet v))) →
      (regularEnvelope G D).neighborSet (v,f)
  | .inl w => ⟨(w.val,f), Or.inl ⟨w.property,rfl⟩⟩
  | .inr i => ⟨(v,flipBit f i.val),Or.inr ⟨rfl,i,rfl⟩⟩

theorem regularEnvelope_degree (bound : ∀ v, Nat.card (G.neighborSet v) ≤ D)
    (v : X) (f : Layer D) : Nat.card ((regularEnvelope G D).neighborSet (v,f)) = D := by
  have bij : Function.Bijective (envelopeNeighbor G D v f) := by
    constructor
    · rintro (a | i) (b | j) h
      · exact congrArg Sum.inl (Subtype.ext (congrArg (fun z => z.val.1) h))
      · exact (G.ne_of_adj a.property (congrArg (fun z => z.val.1) h).symm).elim
      · exact (G.ne_of_adj b.property (congrArg (fun z => z.val.1) h)).elim
      · apply congrArg Sum.inr
        apply Fin.ext
        exact flip_inj f (lt_of_lt_of_le i.isLt (Nat.sub_le _ _)) (congrArg (fun z => z.val.2) h)
    · rintro ⟨⟨w,g⟩, (⟨h,e⟩ | ⟨vw,i,e⟩)⟩
      · exact ⟨.inl ⟨w,h⟩,Subtype.ext (Prod.ext rfl e)⟩
      · exact ⟨.inr i,Subtype.ext (Prod.ext vw e.symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ bij),Nat.card_sum,Nat.card_fin]
  have hv := bound v
  omega

/-- Each layer contains an induced, label-preserving copy of the original graph. -/
def regularEnvelopeEmbedding (f : Layer D) : G ↪g regularEnvelope G D where
  toFun v := (v,f)
  inj' := fun _ _ h => congrArg Prod.fst h
  map_rel_iff' := by
    intro a b
    constructor
    · rintro (⟨h,_⟩ | ⟨_,i,e⟩)
      · exact h
      · exact (self_ne_flip f (lt_of_lt_of_le i.isLt (Nat.sub_le _ _)) e).elim
    · exact fun h => Or.inl ⟨h,rfl⟩

private def envelopePairs (M : G.Subgraph)
    (bound : ∀ v, Nat.card (G.neighborSet v) ≤ D)
    (covers : ∀ v, Nat.card (G.neighborSet v) = D → v ∈ M.verts) :
    (regularEnvelope G D).Subgraph where
  verts := Set.univ
  Adj a b := (M.Adj a.1 b.1 ∧ a.2 = b.2) ∨
    (a.1 = b.1 ∧ a.1 ∉ M.verts ∧ b.2 = flipBit a.2 0)
  adj_sub := by
    rintro ⟨u,f⟩ ⟨v,g⟩ (⟨h,e⟩ | ⟨uv,notMatched,eq⟩)
    · exact Or.inl ⟨M.adj_sub h,e⟩
    · have small := bound u
      have ne : Nat.card (G.neighborSet u) ≠ D := fun h => notMatched (covers u h)
      have pos : 0 < D - Nat.card (G.neighborSet u) := by omega
      exact Or.inr ⟨uv,⟨0,pos⟩,eq⟩
  edge_vert := fun _ => trivial
  symm := ⟨by
    rintro ⟨u,f⟩ ⟨v,g⟩ (⟨h,e⟩ | ⟨uv,notMatched,eq⟩)
    · exact Or.inl ⟨h.symm,e.symm⟩
    · change u = v at uv
      subst v
      exact Or.inr ⟨rfl,notMatched,eq ▸ (flip_twice f 0).symm⟩⟩

omit [Finite X] in
/-- Reuse the original matching at every copy of its support. Pair each remaining
vertex with its twin in direction zero, which is available precisely when needed. -/
theorem regularEnvelope_perfectMatching (M : G.Subgraph) (hM : M.IsMatching)
    (bound : ∀ v, Nat.card (G.neighborSet v) ≤ D)
    (covers : ∀ v, Nat.card (G.neighborSet v) = D → v ∈ M.verts) :
    ∃ N : (regularEnvelope G D).Subgraph, N.IsPerfectMatching := by
  refine ⟨envelopePairs G D M bound covers, SimpleGraph.Subgraph.isPerfectMatching_iff.mpr ?_⟩
  rintro ⟨u,f⟩
  by_cases hu : u ∈ M.verts
  · obtain ⟨w,hw,unique⟩ := hM hu
    refine ⟨(w,f),Or.inl ⟨hw,rfl⟩, ?_⟩
    rintro ⟨z,g⟩ (⟨h,e⟩ | ⟨_,bad,_⟩)
    · exact Prod.ext (unique z h) e.symm
    · exact (bad hu).elim
  · refine ⟨(u,flipBit f 0),Or.inr ⟨rfl,hu,rfl⟩,?_⟩
    rintro ⟨z,g⟩ (⟨h,_⟩ | ⟨uz,_,e⟩)
    · exact (hu (M.edge_vert h)).elim
    · exact Prod.ext uz.symm e

private theorem card_comap_neighbors {U Y : Type*} [Finite Y] (K : SimpleGraph Y) (e : U ↪ Y)
    (v : U) : Nat.card ((K.comap e).neighborSet v) ≤ Nat.card (K.neighborSet (e v)) := by
  apply Nat.card_le_card_of_injective (fun x : (K.comap e).neighborSet v =>
    (⟨e x.val,x.property⟩ : K.neighborSet (e v)))
  intro x y h
  exact Subtype.ext (e.injective (congrArg Subtype.val h))

/-- A spanning ordinary p-factor of the regular envelope gives genuine two-color
degree bounds on the original graph after restricting to the constant-false layer. -/
theorem degreeSplit_of_envelopeFactor (bound : ∀ v, Nat.card (G.neighborSet v) ≤ D)
    (p q : ℕ) (total : p + q = D) (C : SimpleGraph (X × Layer D))
    (sub : C ≤ regularEnvelope G D) (reg : ∀ z, Nat.card (C.neighborSet z) = p) :
    ∃ R : SimpleGraph X, R ≤ G ∧ ∀ v, Nat.card (R.neighborSet v) ≤ p ∧
      Nat.card ((G \ R).neighborSet v) ≤ q := by
  let e := regularEnvelopeEmbedding G D (fun _ => false)
  let R := C.comap e
  have blue : G \ R = (regularEnvelope G D \ C).comap e := by
    ext x y
    change (G.Adj x y ∧ ¬ C.Adj (e x) (e y)) ↔
      ((regularEnvelope G D).Adj (e x) (e y) ∧ ¬ C.Adj (e x) (e y))
    rw [e.map_rel_iff]
  refine ⟨R,fun _ _ h => e.map_rel_iff.mp (sub h),?_⟩
  intro v
  constructor
  · exact (card_comap_neighbors C e.toEmbedding v).trans_eq (reg (e v))
  · rw [blue]
    have card := card_comap_neighbors (regularEnvelope G D \ C) e.toEmbedding v
    have count : Nat.card ((regularEnvelope G D \ C).neighborSet (e v)) +
        Nat.card (C.neighborSet (e v)) = Nat.card ((regularEnvelope G D).neighborSet (e v)) :=
      Set.ncard_sdiff_add_ncard_of_subset (fun _ h => sub h :
        C.neighborSet (e v) ⊆ (regularEnvelope G D).neighborSet (e v))
    have rD : Nat.card ((regularEnvelope G D).neighborSet (e v)) = D :=
      regularEnvelope_degree G D bound v (fun _ => false)
    rw [reg,rD] at count
    have bq : Nat.card ((regularEnvelope G D \ C).neighborSet (e v)) ≤ q := by omega
    exact card.trans bq

/-- On any fixed Tutte cut of a D-regular graph the right-hand side is
D·|T| + p·(|S|−|T|). For one parity class the left-hand side is fixed.
Thus its two feasible endpoint factors suffice for every intermediate bound. -/
theorem between_regular_cut_fees {lo p hi base slope required : ℤ}
    (hl : lo ≤ p) (hh : p ≤ hi) (left : required ≤ base + lo*slope)
    (right : required ≤ base + hi*slope) : required ≤ base + p*slope := by
  by_cases up : 0 ≤ slope
  · exact left.trans (add_le_add_right (mul_le_mul_of_nonneg_right hl up) base)
  · exact right.trans (add_le_add_right (mul_le_mul_of_nonpos_right hh (le_of_not_ge up)) base)

#print axioms between_regular_cut_fees
#print axioms degreeSplit_of_envelopeFactor
#print axioms regularEnvelope_degree
#print axioms regularEnvelopeEmbedding
#print axioms regularEnvelope_perfectMatching
end JSP452Audit.StarHost
