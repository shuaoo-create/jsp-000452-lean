import ResidualOriginalLabels
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit
namespace JSP452Audit.StarHost
open SimpleGraph

/-- All legal corners of the fixed residual are forced on the actual
exterior; one original coloring and one original copy are used per response. -/
theorem fixed_residual_on_sum {s t r : ℕ} {X Y : Type*}
    (B : SimpleGraph X) (H : SimpleGraph Y) (W : RemovalBudget s)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (pm : ∀j,1≤m j)
    (legal : AdmitsInternal W n H)
    (row : ForcingRow (B ⊕g H) s t (padDemand n) (padDemand m) r) :
    ForcingRow B W.len t (padDemand (W.entries n)) (padDemand m) r := by
  intro i j l q idx len jq pos posB R less
  let old := s-i
  have room : W.len≤s := Nat.sub_le _ _
  have length : i+old=s := by dsimp [old];omega
  have orig := row i j old q idx length jq (by omega) posB
  obtain ⟨sub,comp⟩ := JSP452Audit.StarHost.sum_colors less (le_refl H)
  rcases orig _ sub with red|blue
  · let oldN (z:Fin old) := n (originalSuffixLabel i old length.le z)
    have eq : (fun z:Fin old => padDemand n (i+z.val))=oldN := by
      funext z;exact dif_pos (originalSuffixLabel i old length.le z).isLt
    change (forest (fun z:Fin old => padDemand n (i+z.val))).IsContained _ at red
    rw [eq] at red
    obtain ⟨U,left,right⟩ := split_copy_on_sum R H oldN red
    let T : ↥W.choices := ⟨originalRemoved i old length.le Uᶜ,legal i old length.le Uᶜ right⟩
    exact Or.inl (residual_in_surviving_suffix n W R i old l length len U T rfl left)
  · rw [comp,sdiff_self] at blue
    exact Or.inr (copy_in_left_summand (B \ R) _ (forest_has_neighbor (fun z:Fin q => padDemand m (j+z.val))
      (fun z => pad_positive m pm _ (by have := z.isLt;omega))) blue)

/-- Projection to the original exterior after actual root deletion. -/
theorem fixed_residual_on_exterior {s t r D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (W : RemovalBudget s)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (legal : AdmitsInternal W n (G.induce K.core))
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    ForcingRow (G.induce K.rest) W.len t (padDemand (W.entries n)) (padDemand m) (r+K.roots.ncard) := by
  have del := row_delete_set G K.roots _ _ (pad_antitone n hn) (pad_antitone m hm)
    (pad_positive n pn) (pad_positive m pm) row
  obtain ⟨part,dis,sep⟩ := core_rest_partition G K.barrier K.pieces
  have union : K.rest∪K.core=K.rootsᶜ := by rw [Set.union_comm];exact part
  let iso := regionSumIso G K.rootsᶜ K.rest K.core union dis.symm (fun _ hr _ hc e => sep hc hr e.symm)
  exact fixed_residual_on_sum _ _ W n m pm legal (forcingRow_of_iso iso.symm del)

#print axioms fixed_residual_on_sum
#print axioms fixed_residual_on_exterior
end JSP452Audit.StarHost
