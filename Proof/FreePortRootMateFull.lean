import FreeBadPortIncidence
import SaturatedRegion

namespace JSP452Audit.StarHost
open SimpleGraph

/-- On the specified optimal allocation, a root touching any unassigned full
component is itself assigned inside the same attaining full region. -/
theorem incident_free_full_place_full {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀ c : (G.induce Sᶜ).ConnectedComponent,
      Odd (Nat.card c.supp) ∧ PerfectAfterEveryDeletion c.toSimpleGraph)
    (D : ℕ) (A : RootAllocation G S) (opt : (freeFull G S D A).ncard = minimumExposure G D)
    (r : S) (c : (G.induce Sᶜ).ConnectedComponent)
    (free : c ∈ freeFull G S D A) (inc : rootIncidence G S r c) :
    allFullComponent G S D (A.place r) := by
  obtain ⟨T,full,att⟩ := (full_component_deficiency G S tight data D).2
  obtain ⟨roots,exits⟩ := attaining_neighborhood_saturated G S D A T full opt att
  have inside : c ∈ T \ Set.range A.place := exits.symm ▸ free
  have root : r∈rootNeighbors (rootIncidence G S) T := ⟨c,inside.1,inc⟩
  exact full (show r ∈ {a : S | A.place a∈T} from roots.symm ▸ root)

/-- For an original matching realizing the specified root edge, its unique
actual mate at a bad chosen root has full original degree D. -/
theorem chosen_bad_root_mate_full {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀ c : (G.induce Sᶜ).ConnectedComponent,
      Odd (Nat.card c.supp) ∧ PerfectAfterEveryDeletion c.toSimpleGraph)
    (D : ℕ) (A : RootAllocation G S) (opt : (freeFull G S D A).ncard = minimumExposure G D)
    (r : S) (c : (G.induce Sᶜ).ConnectedComponent)
    (free : c∈badFree G S D A) (bad : badPortIncidence G S D r c)
    (M : G.Subgraph) (hm : M.IsMatching) (p : (A.place r).supp) (assigned : M.Adj r.val p.val.val) :
    ∀ w, M.Adj r.val w → Nat.card (G.neighborSet w)=D := by
  have full := incident_free_full_place_full G S tight data D A opt r c free.1
    (badPortIncidence_rootIncidence G S D r c bad)
  intro w edge
  rw [hm.eq_of_adj_left edge assigned]
  exact full p

#print axioms incident_free_full_place_full
#print axioms chosen_bad_root_mate_full
end JSP452Audit.StarHost
