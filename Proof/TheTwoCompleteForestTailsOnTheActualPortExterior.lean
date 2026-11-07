import TenthColumnAndEverySubsequentDeletionOnTheTrueExterior
namespace JSP452Audit.StarHost.TenPortSupport
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {K:TenBlockPartition G} {h:ℕ} (W:TenPortSupport G K h)
theorem complete_blue_tail {s t r : ℕ}
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hm : Antitone m) (pn:∀i,1≤n i) (pm:∀i,1≤m i)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    let μ := W.rank
    ForcingRow W.outside s (t-μ) (padDemand n) (padDemand (remainingDemand m μ)) r := by
  intro μ
  let Z := G \ W.piece
  let T := W.piece
  have rank : matchingEdges T=μ := rfl
  intro i j l q ij il jq pl pq
  apply W.actual_exterior_forces _ _
    (fun a => pad_positive n pn _ (by have := a.isLt;omega))
    (fun b => pad_positive (remainingDemand m μ) (remainingDemand_positive m pm μ) _ (by have := b.isLt;omega))
  intro R incl
  have orig := row i j l (μ+q) ij il (by omega) pl (by omega)
  have recover : G \ R≤(Z \ R)⊔T := by
    intro x y edge
    by_cases old : Z.Adj x y
    · exact Or.inl ⟨old,edge.2⟩
    · exact Or.inr (by by_contra h;exact old ⟨edge.1,h⟩)
  rcases orig R (incl.trans sdiff_le) with red|blue
  · exact Or.inl red
  right
  have kept := trim_touched_forest (Z \ R) T (padDemand m) (pad_antitone m hm) j μ q rank.le (blue.mono_right recover)
  have same : (fun b : Fin q => padDemand (remainingDemand m μ) (j+b.val))=
      (fun b : Fin q => padDemand m (j+μ+b.val)) := by
    funext b;rw [pad_remainingDemand];congr 1;omega
  change (forest (fun b : Fin q => padDemand (remainingDemand m μ) (j+b.val))).IsContained _
  rwa [same]


theorem complete_red_tail {s t r:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (pn:∀i,1≤n i) (pm:∀i,1≤m i)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) :
    ForcingRow W.outside (s-W.rank) t (padDemand (remainingDemand n W.rank)) (padDemand m) r :=
  swap_positive_forcing_row _ _ _ (W.complete_blue_tail m n hn pm pn (swap_positive_forcing_row _ _ _ row))

#print axioms complete_blue_tail
#print axioms complete_red_tail
end JSP452Audit.StarHost.TenPortSupport
