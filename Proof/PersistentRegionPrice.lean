import ExteriorWholeForestStep
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem exterior_deletion_history {s t r D : ℕ} (G : SimpleGraph X) (K : DegreeRegion G D)
    (hs : 0<s) (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (head : n ⟨0,hs⟩=D) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (q : ℕ) (bound : matchingEdges (G.induce K.core)+K.roots.ncard+r+q<t) :
    ∃W:Set X,W⊆K.rest ∧ W.ncard=q ∧ G.IsIndepSet W ∧
      ∀v∈W,Nat.card (G.neighborSet v)=D := by
  induction q with
  | zero => exact ⟨∅,Set.empty_subset _,Set.ncard_empty X,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨W,inside,size,ind,full⟩ := ih (by omega)
    obtain ⟨v,hv,degree,closed⟩ := choose_full_exterior_center G K hs n m hn hm pn pm row head cap
      W inside (by omega)
    refine ⟨insert v W,Set.insert_subset hv.1 inside,?_,?_,?_⟩
    · rw [Set.ncard_insert_of_notMem hv.2,size]
    · rintro a (va|wa) b (vb|wb) ne edge
      · exact ne (va.trans vb.symm)
      · exact (closed (va ▸ edge)).2 wb
      · exact (closed (vb ▸ edge.symm)).2 wa
      · exact ind wa wb ne edge
    · rintro a (e|w)
      · exact e.symm ▸ degree
      · exact full a w

/-- Liu's persistent-region price: at the last exterior deletion the remaining
row is matching-rich and all old exposed full labels still contribute. -/
theorem persistent_region_price {s t r : ℕ} (hs : 0<s) (ht : 0<t) (G : SimpleGraph X)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (live : 0<rowCount s t r)
    (D : ℕ) (degree : D=diagonal n m (r+2)-1) (large : 3≤D) (head : n ⟨0,hs⟩=D)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) (K : DegreeRegion G D)
    (room : matchingEdges (G.induce K.core)+K.roots.ncard+r<t) :
    rowEnergy n m r+minimumExposure G D≤G.edgeSet.ncard+highestWidth n m r := by
  let M := matchingEdges (G.induce K.core)+K.roots.ncard
  let q := t-1-r-M
  have exactLength : M+r+q+1=t := by change M+r<t at room;dsimp [q];omega
  obtain ⟨W,inside,card,ind,full⟩ := exterior_deletion_history G K hs n m hn hm pn pm row head cap q
    (show M+r+q<t by omega)
  have fee := JSP452Audit.StarHost.degree_on_independent_full_set G W D full ind
  rw [card] at fee
  have shifted := row_delete_set G W _ _ (pad_antitone n hn) (pad_antitone m hm)
    (pad_positive n pn) (pad_positive m pm) row
  rw [card] at shifted
  have extCopy := whole_forest_in_surviving_exterior G K hs n m hn hm pn pm row W inside
    (show M+r+W.ncard<t by omega)
  have outside := forest_copy_matching _ n pn extCopy
  rw [Fintype.card_fin] at outside
  obtain ⟨exposure,lower⟩ := ordinary_region_after_exterior_deletions G K W inside
  have count : rowCount s t (r+q)=s+M := by dsimp [rowCount];omega
  have rich : rowCount s t (r+q)≤matchingEdges (G.induce Wᶜ) := by
    change K.roots.ncard+matchingEdges (G.induce K.core)+matchingEdges (G.induce (K.rest\W))≤_ at lower
    dsimp [M] at count;omega
  have remainingCap (u:↥(Wᶜ : Set X)) : Nat.card ((G.induce Wᶜ).neighborSet u)≤D :=
    (induced_neighbor_count_le G Wᶜ u).trans (cap u.val)
  let k := diagonal n m (r+q+2)
  have pay := rich_row_of_envelope_payment hs ht n m hn hm pn pm (G.induce Wᶜ) (r+q) D k shifted
    (by dsimp [k];omega) (finite_host_envelope_reserve (G.induce Wᶜ) D k large remainingCap) rich
  have tax := prefix_column_tax hs ht n m hn hm pn pm r q live
  rw [←degree] at tax
  omega

#print axioms persistent_region_price
end JSP452Audit.StarHost
