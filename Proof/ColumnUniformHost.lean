import HeightColumnPair
import UniformSubforest
import ColumnArea
namespace JSP452Audit.StarHost
open SimpleGraph
/-- A nonempty original column is supported by an actual pair of uniform
forests forced on the same graph, of exactly this height. -/
theorem column_uniform_forcing {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j) {X : Type*} (G : SimpleGraph X)
    (r h : ℕ) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (pos : 0<h) (present : 0<widthAt n m r h) :
    ∃ a b u v : ℕ, 0<a ∧ 0<b ∧ a+b-1=h ∧ 0<u ∧ 0<v ∧
      widthAt n m r h ≤ u+v-1 ∧
      Forces G (forest (fun _ : Fin u => a)) (forest (fun _ : Fin v => b)) := by
  obtain ⟨i,j,a,b,idx,ha,hb,htot,hu,hv,le⟩ := height_column_pair hs ht n m hn hm pn pm r h pos present
  exact ⟨a,b,_,_,ha,hb,htot,hu,hv,le,forces_uniform_subforests G _ _ a b _ _ le_rfl le_rfl
    (forces_original_tails G n m row i j idx)⟩

/-- The area of every original row is the sum of its positive-height widths.
Use one original head from each list as a finite ceiling. -/
theorem row_energy_by_heights {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m) (r : ℕ) :
    rowEnergy n m r = ∑ k ∈ Finset.range (n ⟨0,hs⟩+m ⟨0,ht⟩-1), widthAt n m r (k+1) := by
  apply finite_layer_count (fun k => diagonal n m (r+k+2))
  intro k hk
  obtain ⟨i,j,_,att⟩ := diagonal_attained n m hs ht (r+k) (by dsimp [rowCount] at hk; omega)
  have hi := hn (show (⟨0,hs⟩ : Fin s) ≤ i from Nat.zero_le _)
  have hj := hm (show (⟨0,ht⟩ : Fin t) ≤ j from Nat.zero_le _)
  omega
#print axioms column_uniform_forcing
#print axioms row_energy_by_heights
end JSP452Audit.StarHost