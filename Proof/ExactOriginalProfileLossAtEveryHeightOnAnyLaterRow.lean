import AllThresholdInventoriesMeasureTheSameNestedDeletionSequence
namespace JSP452Audit.StarHost
open SimpleGraph

theorem profile_area_after_any_shift {s t:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) {r b H:ℕ} (later:r≤b) (top:diagonal n m (r+2)≤H) :
    rowEnergy n m b=∑j∈Finset.range H,widthAt n m b (j+1) := by
  apply finite_layer_count
  intro i inside
  have room : b+i<s+t-1 := by dsimp only [rowCount] at inside;omega
  exact (earlier_diagonal_dominates hs ht n m hn hm (show r≤b+i by omega) room).trans top

theorem profile_shift_exact_loss {s t:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) {r b H:ℕ} (later:r≤b) (top:diagonal n m (r+2)≤H) (z:ℕ) :
    rowEnergy n m b=rowEnergy n m (b+z)+∑j∈Finset.range H,min z (widthAt n m b (j+1)) := by
  rw [profile_area_after_any_shift hs ht n m hn hm later top,
    profile_area_after_any_shift hs ht n m hn hm (show r≤b+z by omega) top,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [widthAt_shift hs ht n m hn hm]
  omega

#print axioms profile_area_after_any_shift
#print axioms profile_shift_exact_loss
end JSP452Audit.StarHost
