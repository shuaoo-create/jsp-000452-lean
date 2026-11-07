import OriginalEscapeCoverSurplus
import OriginalUnitAxisArea
namespace JSP452Audit.StarHost
open SimpleGraph

/-- At a legal column the earliest feasible red index is k-(t-1), and
the earliest feasible blue index is k-(s-1). Monochrome colorings force
both values on the current actual graph. -/
def monochromeHeight {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (k : ℕ) : ℕ :=
  max (padDemand n (k-(t-1))) (padDemand m (k-(s-1)))

def deletionColumn {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (k : ℕ) : ℕ :=
  max (diagonal n m (k+2)-1) (monochromeHeight n m k)

private theorem monochrome_blue {s t r : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (pn : ∀i,1≤n i)
    {X : Type*} [Finite X] (G : SimpleGraph X)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (live : r<s+t-1) :
    ∃v,padDemand m (r-(s-1))≤Nat.card (G.neighborSet v) := by
  let j : Fin t := ⟨r-(s-1),by omega⟩
  let i : Fin s := ⟨r-j.val,by dsimp [j];omega⟩
  obtain ⟨v,deg⟩ := select_blue_center G n m pn row i j (by dsimp [i,j];omega)
  exact ⟨v,by rw [padDemand,dif_pos (show r-(s-1)<t by omega)];exact deg⟩

theorem vertex_paying_deletion_column {s t r : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (live : r<s+t-1) : ∃v,deletionColumn n m r≤Nat.card (G.neighborSet v) := by
  have peak := vertex_at_row_peak G hs ht n m pn pm live row
  obtain ⟨b,bdeg⟩ := monochrome_blue hs ht n m pn G row live
  obtain ⟨a,adeg⟩ := monochrome_blue ht hs m n pm G (swap_positive_forcing_row G _ _ row) (by omega)
  obtain ⟨p,pdeg⟩ := peak
  unfold deletionColumn monochromeHeight
  by_cases top : max (padDemand n (r-(t-1))) (padDemand m (r-(s-1)))≤diagonal n m (r+2)-1
  · exact ⟨p,by omega⟩
  by_cases red : padDemand m (r-(s-1))≤padDemand n (r-(t-1))
  · exact ⟨a,by omega⟩
  · exact ⟨b,by omega⟩

/-- Lifting a cover from the actual graph after one deletion costs one
original label. This tracks the same cover reserve down each chosen path. -/
theorem cover_floor_after_deletion {X : Type*} [Finite X] (G : SimpleGraph X) (v : X) (q : ℕ)
    (floor : ∀C,G.IsVertexCover C → q+1≤C.ncard) (Z : Set {x:X|x≠v})
    (cover : (G.induce {x|x≠v}).IsVertexCover Z) : q≤Z.ncard := by
  let f : {x:X|x≠v} → X := Subtype.val
  let C := ({v} : Set X) ∪ f '' Z
  have original : G.IsVertexCover C := by
    intro x y e
    by_cases hx : x∈({v}:Set X)
    · exact Or.inl (Or.inl hx)
    by_cases hy : y∈({v}:Set X)
    · exact Or.inr (Or.inl hy)
    have res : (G.induce {x | x≠v}).Adj ⟨x,hx⟩ ⟨y,hy⟩ := e
    rcases cover res with a|b
    · exact Or.inl (Or.inr ⟨⟨x,hx⟩,a,rfl⟩)
    · exact Or.inr (Or.inr ⟨⟨y,hy⟩,b,rfl⟩)
  have all := floor C original
  have apart : Disjoint ({v}:Set X) (f '' Z) := by
    apply Set.disjoint_left.mpr
    rintro _ mem ⟨z,_,rfl⟩
    exact z.property mem
  dsimp only [C] at all
  rw [Set.ncard_union_eq apart,Set.ncard_singleton,Set.ncard_image_of_injective Z (show Function.Injective f from Subtype.val_injective)] at all
  omega

private theorem cover_floor_edges {X : Type*} [Finite X] (G : SimpleGraph X) (q : ℕ)
    (floor : ∀C,G.IsVertexCover C → q≤C.ncard) : q≤G.edgeSet.ncard := by
  obtain ⟨C,att,cover⟩ := vertexCoverNum_exists G
  have h := vertexCoverNum_le_encard_edgeSet (G:=G)
  rw [←att,←C.toFinite.cast_ncard_eq,←G.edgeSet.toFinite.cast_ncard_eq] at h
  exact (floor C cover).trans (by exact_mod_cast h)

/-- Each deletion occurs in the residual graph from the preceding step.
At zero steps the surviving edges still pay the original cover reserve. -/
theorem cover_deletion_row_sum {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) {X : Type*} [Finite X] (G : SimpleGraph X)
    (r len q : ℕ) (live : r+len≤s+t-1)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (floor : ∀C,G.IsVertexCover C → len+q≤C.ncard) :
    (∑k∈Finset.range len,deletionColumn n m (r+k))+q≤G.edgeSet.ncard := by
  induction len generalizing X r with
  | zero => simpa using cover_floor_edges G q (by simpa using floor)
  | succ k ih =>
    obtain ⟨v,deg⟩ := vertex_paying_deletion_column hs ht n m pn pm G row (by omega)
    have next := row_delete_one G v _ _ (pad_antitone n hn) (pad_antitone m hm)
      (pad_positive n pn) (pad_positive m pm) row
    have residual := ih (G.induce {x | x≠v}) (r+1) (by omega) next
      (cover_floor_after_deletion G v (k+q) (by simpa only [Nat.succ_add,Nat.add_one] using floor))
    have edges := card_neighbor_add_induce_edge_ncard G v
    have shifted : (∑z∈Finset.range k,deletionColumn n m (r+(z+1))) =
        ∑z∈Finset.range k,deletionColumn n m (r+1+z) := by
      apply Finset.sum_congr rfl;intro z _;rw [show r+(z+1)=r+1+z by omega]
    calc
      _ = (∑z∈Finset.range k,deletionColumn n m (r+1+z))+deletionColumn n m r+q := by
        simp only [Finset.sum_range_succ',Nat.add_zero];rw [shifted]
      _ ≤ _ := by omega

#print axioms vertex_paying_deletion_column
#print axioms cover_floor_after_deletion
#print axioms cover_deletion_row_sum
end JSP452Audit.StarHost
