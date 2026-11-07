import CoverDeletionColumnPrice
namespace JSP452Audit.StarHost
universe u

def mixedOffsets {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (r : ℕ) : Finset ℕ :=
  (Finset.range (rowCount s t r)).filter (fun z => monochromeHeight n m (r+z)<diagonal n m (r+z+2))

theorem energy_le_deletion_and_mixed {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (r : ℕ) :
    rowEnergy n m r ≤ (∑z∈Finset.range (rowCount s t r),deletionColumn n m (r+z))+
      (mixedOffsets n m r).card := by
  have col (z : ℕ) : diagonal n m (r+z+2)≤deletionColumn n m (r+z)+
      (if monochromeHeight n m (r+z)<diagonal n m (r+z+2) then 1 else 0) := by
    unfold deletionColumn;split_ifs <;> omega
  have sum := Finset.sum_le_sum (s:=Finset.range (rowCount s t r)) (fun z _ => col z)
  simpa [rowEnergy,Finset.sum_add_distrib,Finset.sum_boole,mixedOffsets] using sum

/-- A strict original row must have more mixed columns than its peak
exposure. In particular some mixed column lies strictly below the top. -/
theorem strict_mixed_columns_exceed_exposure (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    minimumExposure F.G (diagonal F.n F.m (F.r+2)-1)<(mixedOffsets F.n F.m F.r).card ∧
      ∃z,z<F.rank ∧ monochromeHeight F.n F.m (F.r+z)<diagonal F.n F.m (F.r+z+2) ∧
        diagonal F.n F.m (F.r+z+2)<diagonal F.n F.m (F.r+2) := by
  let D := diagonal F.n F.m (F.r+2)-1
  have enough := strict_escape_original_cover F paid K
  have live := F.live
  have legal : F.r+F.rank≤F.s+F.t-1 := by dsimp [StrictFamily.rank,rowCount] at *;omega
  have price := cover_deletion_row_sum F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.rank
    (minimumExposure F.G D) legal F.row enough
  have area := energy_le_deletion_and_mixed F.n F.m F.r
  change rowEnergy F.n F.m F.r≤(∑z∈Finset.range F.rank,deletionColumn F.n F.m (F.r+z))+(mixedOffsets F.n F.m F.r).card at area
  have bad := F.strict
  have many : minimumExposure F.G D<(mixedOffsets F.n F.m F.r).card := by omega
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have width := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).2
  change (highestOffsets F.n F.m F.r).card≤minimumExposure F.G D at width
  have outside : ¬ mixedOffsets F.n F.m F.r⊆highestOffsets F.n F.m F.r := by
    intro sub;have := Finset.card_le_card sub;omega
  obtain ⟨z,mem,missing⟩ := Finset.not_subset.mp outside
  obtain ⟨within,gap⟩ := Finset.mem_filter.mp mem
  have zlt : z<F.rank := Finset.mem_range.mp within
  have capD := earlier_diagonal_dominates F.hs F.ht F.n F.m F.hn F.hm (show F.r≤F.r+z by omega)
    (show F.r+z<F.s+F.t-1 by omega)
  have ne : diagonal F.n F.m (F.r+z+2) ≠ diagonal F.n F.m (F.r+2) :=
    fun eq => missing (Finset.mem_filter.mpr ⟨within,eq⟩)
  exact ⟨many,z,zlt,gap,by omega⟩

#print axioms energy_le_deletion_and_mixed
#print axioms strict_mixed_columns_exceed_exposure
end JSP452Audit.StarHost
