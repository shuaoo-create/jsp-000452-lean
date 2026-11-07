import PositiveRootDebt
namespace JSP452Audit.StarHost
open SimpleGraph
/-- Delete a set of actual original labels without changing the host of the resulting row. -/
theorem row_delete_set {X : Type*} [Finite X] {s t r : ℕ} (G : SimpleGraph X) (U : Set X)
    (n m : ℕ → ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀ i<s, 0<n i) (pm : ∀ j<t, 0<m j)
    (row : ForcingRow G s t n m r) : ForcingRow (G.induce Uᶜ) s t n m (r+U.ncard) := by
  classical
  let F := U.toFinite.toFinset
  have w : ({x | x∉F} : Set X)=Uᶜ := by ext x; simp [F]
  have count : F.card=U.ncard := by rw [← Set.ncard_coe_finset,U.toFinite.coe_toFinset]
  have res := row_delete_finset G F n m hn hm pn pm row
  rwa [w,count] at res

/-- Source-level use of the root inequality with the *actual* top-column width. -/
theorem critical_root_debt {X : Type*} [Finite X] {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j) (G : SimpleGraph X) (r : ℕ)
    (live : 0<rowCount s t r) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ diagonal n m (r+2)-1)
    (K : DegreeRegion G (diagonal n m (r+2)-1)) :
    let D := diagonal n m (r+2)-1
    (rootShortfall G K.roots D:ℤ) + ((G.induce K.roots).edgeSet.ncard:ℤ) + highestWidth n m r ≤
      2*edgeSurplus (G.induce K.positiveCore) D - ((D:ℤ)-1)*(minimumExposure G D:ℤ) :=
  K.root_debt cap _ (row_minimum_exposure hs ht n m hn hm pn pm G r live row cap).2
#print axioms row_delete_set
#print axioms critical_root_debt
end JSP452Audit.StarHost