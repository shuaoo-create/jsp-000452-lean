import NinePortGapAndTwoExteriorStages
import EndpointStageThresholdCount
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- On an overlapping pair of edge palettes, force the full forest in Y or
retain at least the indicated matching rank in its other color. Shared vertices
are allowed. The estimate uses the matching rank of the actual other palette. -/
theorem edge_palette_forest_endpoint {X : Type*} [Finite X] (G Y J : SimpleGraph X)
    (sub : Y≤G) (cover : G≤Y⊔J) {s t r : ℕ} (hs : 0<s) (legal : r<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (pm : ∀i,1≤m i)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    ForestMatchingEndpoint Y n (t-r-matchingEdges J) := by
  intro A incl
  have orig := row 0 r s (t-r) (by omega) (by omega) (by omega) hs (by omega)
  rcases orig A (incl.trans sub) with found|other
  · left
    have eq : (fun i : Fin s => padDemand n (0+i.val))=n := by funext i;simp [padDemand,i.isLt]
    change (forest (fun i : Fin s => padDemand n (0+i.val))).IsContained A at found
    rwa [eq] at found
  · right
    have bound := forest_copy_matching (G \ A) (fun j : Fin (t-r) => padDemand m (r+j.val))
      (fun j => pad_positive m pm _ (by have := j.isLt;omega)) other
    rw [Fintype.card_fin] at bound
    have cap := rank_of_two_edge_colours (G \ A) (Y \ A) J (by
      intro x y e
      rcases cover e.1 with yEdge|jEdge
      · exact Or.inl ⟨yEdge,e.2⟩
      · exact Or.inr jEdge)
    omega

theorem positive_endpoint_rank {X : Type*} [Finite X] (Y : SimpleGraph X) {s q : ℕ}
    (hs : 0<s) (n : Fin s→ℕ) (pn : ∀i,1≤n i) (endpt : ForestMatchingEndpoint Y n q) :
    q≤matchingEdges Y := by
  have test := endpt ⊥ bot_le
  have noCopy : ¬(forest n).IsContained (⊥ : SimpleGraph X) := by
    rintro ⟨f⟩
    let i : Fin s := ⟨0,hs⟩
    let j : Fin (n i) := ⟨0,pn i⟩
    exact f.toHom.map_adj (starEdge n ⟨i,j⟩)
  simpa only [sdiff_bot] using test.resolve_left noCopy

theorem endpoint_stage_inventory {X : Type*} [Finite X] (Y : SimpleGraph X) {s q d p : ℕ}
    (hs : 0<s) (n : Fin s→ℕ) (pn : ∀i,1≤n i) (endpt : ForestMatchingEndpoint Y n q)
    (pos : 0<d) (hq : 0<q) (account : matchingEdges Y+d+1=s+q)
    (T : Set X) (cap : ∀v : ↥(Tᶜ : Set X),Nat.card ((Y.induce Tᶜ).neighborSet v)≤p)
    (live : 0<originalThresholdCount n (p+1)) :
    2*(d+∑i,(n i-1)/2)+originalThresholdCount n (p+1)≤T.ncard+1 := by
  have parity := endpoint_forest_parity_cost Y n pn endpt pos hq (positive_endpoint_rank Y hs n pn endpt) account
  have count := endpoint_threshold_stage Y n pn endpt hq T cap live
  omega

#print axioms edge_palette_forest_endpoint
#print axioms positive_endpoint_rank
#print axioms endpoint_stage_inventory
end JSP452Audit.StarHost
