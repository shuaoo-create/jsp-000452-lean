import WholeCoreErasureRank
import TrimTouchedForest
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

def remainingDemand {t : ℕ} (m : Fin t→ℕ) (k : ℕ) (j : Fin (t-k)) : ℕ :=
  padDemand m (k+j.val)

theorem remainingDemand_antitone {t : ℕ} (m : Fin t→ℕ) (hm : Antitone m) (k : ℕ) :
    Antitone (remainingDemand m k) := fun _ _ h => pad_antitone m hm (Nat.add_le_add_left h k)

theorem remainingDemand_positive {t : ℕ} (m : Fin t→ℕ) (pm : ∀j,1≤m j) (k : ℕ)
    (i : Fin (t-k)) : 1≤remainingDemand m k i :=
  pad_positive m pm _ (by have hi:=i.isLt;omega)

theorem pad_remainingDemand {t : ℕ} (m : Fin t→ℕ) (k j : ℕ) :
    padDemand (remainingDemand m k) j=padDemand m (k+j) := by
  by_cases inside : j<t-k
  · rw [padDemand,dif_pos inside];rfl
  · have beyond : ¬k+j<t := by omega
    simp [padDemand,inside,beyond]

/-- Retain all original labels and restore every erased internal edge blue.
At most μ stars of any blue copy use a restored edge. -/
theorem erase_core_complete_blue_row {s t r D : ℕ} (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hm : Antitone m)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    let μ := matchingEdges (G.induce K.core)
    ForcingRow (eraseInternal G K.core) s (t-μ) (padDemand n) (padDemand (remainingDemand m μ)) r := by
  intro μ
  let Z := eraseInternal G K.core
  let T := G \ Z
  have rank : matchingEdges T=μ := rank_of_internal_edges G K.core
  intro i j l q ij il jq pl pq R incl
  have orig := row i j l (μ+q) ij il (by omega) pl (by omega)
  have recover : G \ R≤(Z \ R)⊔T := by
    intro x y edge
    by_cases old : Z.Adj x y
    · exact Or.inl ⟨old,edge.2⟩
    · exact Or.inr ⟨edge.1,old⟩
  rcases orig R (incl.trans (eraseInternal_le G K.core)) with red|blue
  · exact Or.inl red
  right
  have kept := trim_touched_forest (Z \ R) T (padDemand m) (pad_antitone m hm) j μ q rank.le (blue.mono_right recover)
  have same : (fun b : Fin q => padDemand (remainingDemand m μ) (j+b.val))=
      (fun b : Fin q => padDemand m (j+μ+b.val)) := by
    funext b;rw [pad_remainingDemand];congr 1;omega
  change (forest (fun b : Fin q => padDemand (remainingDemand m μ) (j+b.val))).IsContained _
  rwa [same]

theorem erase_core_complete_red_row {s t r D : ℕ} (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    let μ := matchingEdges (G.induce K.core)
    ForcingRow (eraseInternal G K.core) (s-μ) t (padDemand (remainingDemand n μ)) (padDemand m) r := by
  intro μ
  have flip := erase_core_complete_blue_row G K m n hn (swap_positive_forcing_row G _ _ row)
  exact swap_positive_forcing_row _ _ _ flip

#print axioms pad_remainingDemand
#print axioms erase_core_complete_blue_row
#print axioms erase_core_complete_red_row
end JSP452Audit.StarHost
