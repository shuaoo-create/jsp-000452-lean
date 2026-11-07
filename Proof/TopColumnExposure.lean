import RowExposure
import MinimumExposure
import HighestColumn
namespace JSP452Audit.StarHost
open SimpleGraph
/-- The width of the top column is paid in genuinely exposed full-degree vertices
by every matching of the same original host. -/
theorem highest_width_le_exposure {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (r : ℕ) (live : 0<rowCount s t r)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (bound : ∀ x, Nat.card (G.neighborSet x) ≤ diagonal n m (r+2)-1)
    (M : G.Subgraph) (hM : M.IsMatching) :
    highestWidth n m r ≤ (exposedFull G M (diagonal n m (r+2)-1)).ncard := by
  obtain ⟨i,j,sum,att,width⟩ := highest_column_head_pair hs ht n m hn hm pn pm r live
  exact width.trans (suffix_pair_exposure G M hM n m pn pm row bound i j sum att)

/-- In particular the top column controls the minimum among maximum matchings,
not merely a chosen witness. The positive lower bound includes nonempty rank one. -/
theorem row_minimum_exposure {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (r : ℕ) (live : 0<rowCount s t r)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (bound : ∀ x, Nat.card (G.neighborSet x) ≤ diagonal n m (r+2)-1) :
    1 ≤ highestWidth n m r ∧ highestWidth n m r ≤ minimumExposure G (diagonal n m (r+2)-1) := by
  constructor
  · exact Finset.card_pos.mpr ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr live,by simp⟩⟩
  · apply (le_minimumExposure_iff G _ _).mpr
    intro M hM _
    exact highest_width_le_exposure hs ht n m hn hm pn pm G r live row bound M hM
#print axioms highest_width_le_exposure
#print axioms row_minimum_exposure
end JSP452Audit.StarHost