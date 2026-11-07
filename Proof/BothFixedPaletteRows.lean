import OneColorSpecificErasedResponse
namespace JSP452Audit.StarHost
open SimpleGraph

private theorem single_palette_projection {s i old l D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (R P : SimpleGraph X) (less : R≤eraseInternal G K.core) (sub : P≤restoredInternal G K)
    (W : RemovalBudget s) (n : Fin s→ℕ) (hn : Antitone n) (pn : ∀z,1≤n z)
    (adm : AdmitsInternal W n (P.induce K.core)) (len : i+old=s) (fits : i+l=W.len)
    (copy : (suffixStars (padDemand n) i old).IsContained (R⊔P)) :
    (suffixStars (padDemand (commonErasedDemand n W K.roots.ncard (matchingEdges P))) i l).IsContained R := by
  let oldN (z:Fin old) := n (originalSuffixLabel i old len.le z)
  have eq : (fun z:Fin old => padDemand n (i+z.val))=oldN := by
    funext z;exact dif_pos (originalSuffixLabel i old len.le z).isLt
  change (forest (fun z:Fin old => padDemand n (i+z.val))).IsContained _ at copy
  rw [eq] at copy
  obtain ⟨f⟩ := copy
  exact colored_erased_response G K R P less sub W n hn pn adm len fits f

/-- The original complement after restoring P has only its surviving
exterior-blue edges and the blue part of the same internal palette. -/
theorem fixed_palette_erased_row {s t r D : ℕ} {X : Type*} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (P : SimpleGraph X) (sub : P≤restoredInternal G K)
    (W : RemovalBudget s) (V : RemovalBudget t) (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀z,1≤n z) (pm : ∀z,1≤m z) (red : AdmitsInternal W n (P.induce K.core))
    (blue : AdmitsInternal V m (((restoredInternal G K) \ P).induce K.core))
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    let Q := (restoredInternal G K) \ P
    ForcingRow (eraseInternal G K.core) W.len V.len
      (padDemand (commonErasedDemand n W K.roots.ncard (matchingEdges P)))
      (padDemand (commonErasedDemand m V K.roots.ncard (matchingEdges Q))) r := by
  intro Q i j l q ij il jq pl pq R less
  let Z := eraseInternal G K.core
  have sl : W.len≤s := Nat.sub_le _ _
  have tl : V.len≤t := Nat.sub_le _ _
  let oldR := s-i
  let oldB := t-j
  have lenR : i+oldR=s := by dsimp [oldR];omega
  have lenB : j+oldB=t := by dsimp [oldB];omega
  have orig := row i j oldR oldB ij lenR lenB (by omega) (by omega)
  have restored : R⊔P≤G := sup_le (less.trans (eraseInternal_le G K.core)) (sub.trans sdiff_le)
  have comp : G \ (R⊔P)≤(Z \ R)⊔Q := by
    intro x y e
    by_cases before : Z.Adj x y
    · exact Or.inl ⟨before,fun r => e.2 (Or.inl r)⟩
    · exact Or.inr ⟨⟨e.1,before⟩,fun p => e.2 (Or.inr p)⟩
  rcases orig _ restored with rr|bb
  · exact Or.inl (single_palette_projection G K R P less sub W n hn pn red lenR il rr)
  · exact Or.inr (single_palette_projection G K (Z \ R) Q sdiff_le sdiff_le V m hm pm blue lenB jq (bb.mono_right comp))

theorem palette_complement_inside {X : Type*} [Finite X] (G : SimpleGraph X)
    {D : ℕ} (K : DegreeRegion G D) (P : SimpleGraph X) :
    ((restoredInternal G K) \ P).induce K.core=(G.induce K.core) \ P.induce K.core := by
  ext a b
  change ((G.Adj a.val b.val ∧ ¬(G.Adj a.val b.val ∧ ¬(a.val∈K.core ∧ b.val∈K.core))) ∧ ¬P.Adj a.val b.val) ↔
    (G.Adj a.val b.val ∧ ¬P.Adj a.val b.val)
  have ha := a.property;have hb := b.property
  tauto

/-- Both successor rows apply to exactly the same palette and retain
their own vertex labels, independent of the coloring of each successor. -/
theorem both_fixed_palette_rows {s t r D : ℕ} {X : Type*} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (P : SimpleGraph X) (sub : P≤restoredInternal G K)
    (W : RemovalBudget s) (V : RemovalBudget t) (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀z,1≤n z) (pm : ∀z,1≤m z) (red : AdmitsInternal W n (P.induce K.core))
    (blue : AdmitsInternal V m (((restoredInternal G K) \ P).induce K.core))
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    let Q := (restoredInternal G K) \ P
    ForcingRow (G.induce K.rest) W.len V.len (padDemand (W.entries n)) (padDemand (V.entries m)) (r+K.roots.ncard) ∧
      ForcingRow (eraseInternal G K.core) W.len V.len (padDemand (commonErasedDemand n W K.roots.ncard (matchingEdges P)))
      (padDemand (commonErasedDemand m V K.roots.ncard (matchingEdges Q))) r := by
  intro Q
  have cap : P.induce K.core≤G.induce K.core := fun _ _ h => (sub h).1
  refine ⟨two_budget_exterior_row G K _ cap n m hn hm pn pm W V red ?_ row,?_⟩
  · rw [←palette_complement_inside];exact blue
  · exact fixed_palette_erased_row G K P sub W V n m hn hm pn pm red blue row

#print axioms fixed_palette_erased_row
#print axioms palette_complement_inside
#print axioms both_fixed_palette_rows
end JSP452Audit.StarHost
