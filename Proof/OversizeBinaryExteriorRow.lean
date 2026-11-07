import OversizeBinarySelection
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit
namespace JSP452Audit.StarHost
open SimpleGraph

private theorem binary_initial_corner {X Y : Type*} [Finite X] [Finite Y]
    {s : ℕ} (R : SimpleGraph X) (H : SimpleGraph Y) (n : Fin s→ℕ) (pn : ∀i,1≤n i)
    (large : Nat.card Y<nonunitOrder n) (copy : (forest n).IsContained (R ⊕g H))
    {l : ℕ} (len : l=s-matchingEdges H) (pos : 0<l) :
    (forest (@oneBinaryHead l)).IsContained R := by
  classical
  obtain ⟨U,left,right⟩ := split_copy_on_sum R H n copy
  let _ := Fintype.ofFinite ↥U
  have lower := split_left_has_length n pn H U right
  have big := oversize_nonunit_lands_left n H U right large
  exact select_binary_left R (fun i:U => n i.val) (fun i => pn i.val) l pos
    (by rw [←Nat.card_eq_fintype_card];change l≤U.ncard;omega) big left

/-- When the full nonunit subforest cannot fit in the core, replacing
the first red exterior unit by a two-leaf star gives a genuine entire
row on B with the same lengths and the full original opposite list. -/
theorem oversize_binary_exterior {s t r D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (large : K.core.ncard<nonunitOrder n) :
    let μ := matchingEdges (G.induce K.core)
    ForcingRow (G.induce K.rest) (s-μ) t (padDemand (@oneBinaryHead (s-μ))) (padDemand m) (r+K.roots.ncard) := by
  intro μ
  let Gc := G.induce K.core
  let B := G.induce K.rest
  have coarse := exterior_complete_red_tail G K n m hn hm pn pm row
  have del := row_delete_set G K.roots _ _ (pad_antitone n hn) (pad_antitone m hm)
    (pad_positive n pn) (pad_positive m pm) row
  obtain ⟨part,dis,sep⟩ := core_rest_partition G K.barrier K.pieces
  have union : K.rest∪K.core=K.rootsᶜ := by rw [Set.union_comm];exact part
  let iso := regionSumIso G K.rootsᶜ K.rest K.core union dis.symm (fun _ hr _ hc e => sep hc hr e.symm)
  have actual := forcingRow_of_iso iso.symm del
  intro i j l q idx len other pos posb R sub
  by_cases zero : i=0
  · subst i
    have initial := actual 0 j s q idx (Nat.zero_add s) other (by omega) posb
    obtain ⟨less,complement⟩ := JSP452Audit.StarHost.sum_colors sub (le_refl Gc)
    rcases initial _ less with red|blue
    · have origin : (fun u:Fin s => padDemand n (0+u.val))=n := by funext u;simp [padDemand,u.isLt]
      change (forest (fun u:Fin s => padDemand n (0+u.val))).IsContained _ at red
      rw [origin] at red
      have bin := binary_initial_corner R Gc n pn large red (by change l=s-μ;omega) pos
      have same : (fun z:Fin l => padDemand (@oneBinaryHead (s-μ)) (0+z.val))=@oneBinaryHead l := by
        funext z
        have zl := z.isLt
        simp only [Nat.zero_add,padDemand,dif_pos (show z.val<s-μ by omega),oneBinaryHead]
      left
      change (forest (fun z:Fin l => padDemand (@oneBinaryHead (s-μ)) (0+z.val))).IsContained R
      rw [same]
      exact bin
    · right
      rw [complement,sdiff_self] at blue
      exact copy_in_left_summand (B \ R) _ (forest_has_neighbor (fun x:Fin q => padDemand m (j+x.val))
        (fun x => pad_positive m pm _ (by have := x.isLt;omega))) blue
  · rcases coarse i j l q idx len other pos posb R sub with red|blue
    · left
      let u (z:Fin l) := padDemand (@oneBinaryHead (s-μ)) (i+z.val)
      let v (z:Fin l) := padDemand (remainingDemand n μ) (i+z.val)
      have fit (z:Fin l) : u z≤v z := by
        have zl := z.isLt
        have within : i+z.val<s-μ := by omega
        have one : u z=1 := by
          dsimp [u];rw [padDemand,dif_pos within];simp [oneBinaryHead,zero]
        rw [one];exact pad_positive _ (remainingDemand_positive n pn μ) _ within
      let sel := subforestCopy u v (Function.Embedding.refl _) fit
      exact (show (forest u).IsContained (forest v) from ⟨sel⟩).trans red
    · exact Or.inr blue

#print axioms oversize_binary_exterior
end JSP452Audit.StarHost
