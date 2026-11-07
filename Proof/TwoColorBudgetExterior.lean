import FullEscapingHeadMixedBoundary
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit
namespace JSP452Audit.StarHost
open SimpleGraph

private theorem one_sum_residual {s i l old : ℕ} {X Y : Type*} (R : SimpleGraph X) (H : SimpleGraph Y)
    (n : Fin s→ℕ) (W : RemovalBudget s) (len : i+old=s) (fits : i+l=W.len)
    (adm : AdmitsInternal W n H)
    (copy : (suffixStars (padDemand n) i old).IsContained (R⊕g H)) :
    (suffixStars (padDemand (W.entries n)) i l).IsContained R := by
  let oldN (z:Fin old) := n (originalSuffixLabel i old len.le z)
  have eq : (fun z:Fin old => padDemand n (i+z.val))=oldN := by
    funext z;exact dif_pos (originalSuffixLabel i old len.le z).isLt
  change (forest (fun z:Fin old => padDemand n (i+z.val))).IsContained _ at copy
  rw [eq] at copy
  obtain ⟨U,left,right⟩ := split_copy_on_sum R H oldN copy
  let T : ↥W.choices := ⟨_,adm i old len.le Uᶜ right⟩
  exact residual_in_surviving_suffix n W R i old l len fits U T rfl left

/-- Fix the internal palette before testing any exterior coloring. Both
complete residual lists are chosen once and cover every legal corner. -/
theorem two_budget_exterior_row {s t r D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (P : SimpleGraph K.core) (sub : P≤G.induce K.core)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (W : RemovalBudget s) (V : RemovalBudget t) (red : AdmitsInternal W n P)
    (blue : AdmitsInternal V m ((G.induce K.core) \ P))
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    ForcingRow (G.induce K.rest) W.len V.len (padDemand (W.entries n)) (padDemand (V.entries m))
      (r+K.roots.ncard) := by
  have del := row_delete_set G K.roots _ _ (pad_antitone n hn) (pad_antitone m hm)
    (pad_positive n pn) (pad_positive m pm) row
  obtain ⟨part,dis,sep⟩ := core_rest_partition G K.barrier K.pieces
  have union : K.rest∪K.core=K.rootsᶜ := by rw [Set.union_comm];exact part
  let iso := regionSumIso G K.rootsᶜ K.rest K.core union dis.symm (fun _ hr _ hc e => sep hc hr e.symm)
  have actual := forcingRow_of_iso iso.symm del
  intro i j l q ij il jq pl pq R less
  have nlen : W.len≤s := Nat.sub_le _ _
  have mlen : V.len≤t := Nat.sub_le _ _
  let oldR := s-i
  let oldB := t-j
  have lenR : i+oldR=s := by dsimp [oldR];omega
  have lenB : j+oldB=t := by dsimp [oldB];omega
  have orig := actual i j oldR oldB ij lenR lenB (by omega) (by omega)
  obtain ⟨both,comp⟩ := JSP452Audit.StarHost.sum_colors less sub
  rcases orig _ both with redCopy|blueCopy
  · exact Or.inl (one_sum_residual R P n W lenR il red redCopy)
  · rw [comp] at blueCopy
    exact Or.inr (one_sum_residual _ _ m V lenB jq blue blueCopy)

#print axioms two_budget_exterior_row
end JSP452Audit.StarHost
