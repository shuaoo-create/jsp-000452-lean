import UniformAccounting
import TrimMatchingCopy
import EraseRestoration
import UniformProfileStep
import SharpProfiles

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Erasing any actual matching from a forcing host diminishes every red
    target by one leaf and keeps the complete blue alternative on that host. -/
theorem forcing_erase_matching {I J X : Type*} (G : SimpleGraph X) (M : G.Subgraph) (hM : M.IsMatching)
    (n : I → ℕ) (m : J → ℕ) (h : Forces G (forest (fun i => n i + 1)) (forest m)) :
    Forces (G \ M.spanningCoe) (forest n) (forest m) := by
  intro R hr
  rcases h _ (restoreMatching_red_le M hr) with red | blue
  · exact Or.inl (trim_matching_copy M hM n red)
  · rw [restoreMatching_blue_eq] at blue
    exact Or.inr blue

/-- This transfer applies to nonuniform lists too. Its only unresolved input
    is the exact lower inequality for the shorter-leaf instance. -/
theorem exact_add_red_one {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (nPos : ∀ i, 1≤n i) (mWide : ∀ j, 2≤m j)
    (smaller : sizeRamsey (forest n) (forest m) = ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k) :
    sizeRamsey (forest (fun i => n i+1)) (forest m) =
      ∑ k ∈ Finset.Icc 2 (s+t), diagonal (fun i => n i+1) m k := by
  apply exact_of_forcing_lower
  intro N G h
  obtain ⟨M,hM,count⟩ := large_matching_for_erase hs ht _ _ (fun i => by have := nPos i; omega) mWide G h
  have less := forcing_erase_matching G M hM n m h
  have previous := sizeRamsey_le_of_host _ _ _ less
  rw [smaller] at previous
  have step := profile_red_add hs ht n m (fun j => by have := mWide j; omega) 1
  have parts := eraseMatching_edge_count M
  rw [step]
  omega

theorem exact_add_red_shift {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (nPos : ∀ i, 1≤n i) (mWide : ∀ j, 2≤m j)
    (smaller : sizeRamsey (forest n) (forest m) = ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k)
    (d : ℕ) :
    sizeRamsey (forest (fun i => n i+d)) (forest m) =
      ∑ k ∈ Finset.Icc 2 (s+t), diagonal (fun i => n i+d) m k := by
  induction d with
  | zero => simpa using smaller
  | succ d ih =>
    exact exact_add_red_one hs ht _ _ (fun i => by have := nPos i; dsimp; omega) mWide ih

theorem uniform_vs_unit_free {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (a : ℕ) (positive : 1≤a) (m : Fin t → ℕ) (hm : Antitone m) (mWide : ∀ j, 2≤m j) :
    sizeRamsey (forest (fun _ : Fin s => a)) (forest m) =
      ∑ k ∈ Finset.Icc 2 (s+t), diagonal (fun _ : Fin s => a) m k := by
  have base := matching_forest_exact hs ht (fun _ : Fin s => 1) m antitone_const hm
    (by intro; decide) (fun j => by have := mWide j; omega) (Or.inl (by intro; rfl))
  have h := exact_add_red_shift hs ht (fun _ : Fin s => 1) m (by intro; decide) mWide base (a-1)
  have eq : (fun _ : Fin s => 1+(a-1)) = (fun _ : Fin s => a) := funext fun _ => by omega
  rw [eq] at h
  exact h

theorem unit_free_vs_uniform {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (hn : Antitone n) (nWide : ∀ i, 2≤n i) (a : ℕ) (positive : 1≤a) :
    sizeRamsey (forest n) (forest (fun _ : Fin t => a)) =
      ∑ k ∈ Finset.Icc 2 (s+t), diagonal n (fun _ : Fin t => a) k := by
  apply exact_of_forcing_lower
  intro N G h
  have b := sizeRamsey_le_of_host _ _ _ (forces_swap h)
  rw [uniform_vs_unit_free ht hs a positive n hn nWide] at b
  simpa only [Nat.add_comm t s,diagonal_swap (fun _ : Fin t => a) n] using b

#print axioms exact_add_red_shift
#print axioms uniform_vs_unit_free
#print axioms unit_free_vs_uniform
end JSP452Audit.StarHost
