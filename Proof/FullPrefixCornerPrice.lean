import DominatingBlueEndpoint
import CubicBinaryPeak
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- One original split simultaneously destroys all D-leaf red stars.
The blue matching number is at most the number of vertices chosen. -/
theorem dominated_full_red_split (G : SimpleGraph X) (D : ℕ) (positive : 0<D)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) (S : Set X)
    (dom : ∀v,Nat.card (G.neighborSet v)=D → v∈S ∨ ∃w∈S,G.Adj v w) :
    ∃R:SimpleGraph X,R≤G ∧ (∀v,Nat.card (R.neighborSet v)<D) ∧ matchingEdges (G \ R)≤S.ncard := by
  classical
  let R : SimpleGraph X := {
    Adj := fun x y => G.Adj x y ∧ x∉S ∧ y∉S
    symm := ⟨fun _ _ e => ⟨e.1.symm,e.2.2,e.2.1⟩⟩
    loopless := ⟨fun _ e => G.irrefl e.1⟩ }
  have sub : R≤G := fun _ _ e => e.1
  have redSmall (v:X) : Nat.card (R.neighborSet v)<D := by
    by_cases removed : v∈S
    · have empty : R.neighborSet v=∅ := Set.eq_empty_iff_forall_notMem.mpr (fun w e => e.2.1 removed)
      rw [Nat.card_coe_set_eq,empty,Set.ncard_empty];exact positive
    have subset : R.neighborSet v⊆G.neighborSet v := fun _ e => e.1
    by_cases full : Nat.card (G.neighborSet v)=D
    · obtain ⟨w,ws,e⟩ := (dom v full).resolve_left removed
      have strict : R.neighborSet v ⊂ G.neighborSet v := ⟨subset,fun back => (back e).2.2 ws⟩
      exact (show Nat.card (R.neighborSet v)<Nat.card (G.neighborSet v) from Set.ncard_lt_ncard strict).trans_eq full
    · exact (show Nat.card (R.neighborSet v)≤Nat.card (G.neighborSet v) from Set.ncard_le_ncard subset).trans_lt
        (lt_of_le_of_ne (cap v) full)
  have blueCover : matchingEdges (G \ R)≤S.ncard := matchingEdges_le_cover_card _ S (by
    intro x y e
    by_cases xs:x∈S
    · exact Or.inl xs
    · exact Or.inr (Classical.byContradiction (fun ys => e.2 ⟨e.1,xs,ys⟩)))
  exact ⟨R,sub,redSmall,blueCover⟩

/-- Every actual corner whose first remaining red star has D leaves
forces its whole blue suffix when the red maximum degree is below D. -/
theorem cubic_full_corner_blue_copy {s t r D : ℕ} (G R : SimpleGraph X)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (i:Fin s) (j:Fin t) (sum:i.val+j.val=r) (head:n i=D)
    (sub:R≤G) (redSmall : ∀v,Nat.card (R.neighborSet v)<D) :
    (forest (originalTail m j)).IsContained (G \ R) := by
  rcases forces_original_tails G n m row i j sum R sub with red|blue
  · obtain ⟨f⟩ := red
    let z : Fin (s-i.val) := ⟨0,by have := i.isLt;omega⟩
    obtain ⟨w⟩ := oneStar_in_forest (originalTail n i) z
    let g := f.comp w
    have large := star_copy_center_degree R g
    have small := redSmall (g (center (fun _ : Fin 1 => originalTail n i z) 0))
    have degree : originalTail n i z=D := by simpa [originalTail,z,padDemand,i.isLt] using head
    omega
  · exact blue

/-- Use the last legal corner retaining a full red head, rather than
paying only the unshifted blue endpoint. -/
theorem full_prefix_dominating_price {s t r D : ℕ} (G : SimpleGraph X) (hs : 0<s)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (pm : ∀v,1≤m v)
    (active : r<t) (cap : ∀v,Nat.card (G.neighborSet v)≤D) (positive : 0<D)
    (ncap : n ⟨0,hs⟩=D) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (S:Set X) (dom : ∀v,Nat.card (G.neighborSet v)=D → v∈S ∨ ∃w∈S,G.Adj v w) :
    t-r+min r (originalThresholdCount n D-1)≤S.ncard := by
  let P := originalThresholdCount n D
  let l := min r (P-1)
  have pos : 0<P := (original_threshold_prefix n hn D ⟨0,hs⟩).1 ncap.ge
  have bound : l<P := by dsimp [l];omega
  have ps : P≤s := original_threshold_le_length n D
  let i : Fin s := ⟨l,bound.trans_le ps⟩
  let j : Fin t := ⟨r-l,by omega⟩
  have first : n i=D := le_antisymm ((hn (show (⟨0,hs⟩:Fin s)≤ i from Nat.zero_le _)).trans_eq ncap)
    ((original_threshold_prefix n hn D i).2 bound)
  have idx : i.val+j.val=r := by dsimp [i,j,l];omega
  obtain ⟨R,sub,red,blue⟩ := dominated_full_red_split G D positive cap S dom
  have f := cubic_full_corner_blue_copy G R n m row i j idx first sub red
  have matching := forest_copy_matching (G \ R) (originalTail m j)
    (fun v => pad_positive m pm _ (by have := v.isLt;have := j.isLt;omega)) f
  rw [Fintype.card_fin] at matching
  change t-(r-l)≤matchingEdges (G \ R) at matching
  change t-r+l≤S.ncard
  have before : l≤r := Nat.min_le_left _ _
  omega

#print axioms dominated_full_red_split
#print axioms cubic_full_corner_blue_copy
#print axioms full_prefix_dominating_price
end JSP452Audit.StarHost
