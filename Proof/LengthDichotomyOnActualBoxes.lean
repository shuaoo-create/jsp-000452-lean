import ShortForestInTheTwoActualBoxes
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem deficient_sum_row_length_dichotomy {X Y:Type*} [Finite X] [Finite Y] (C:SimpleGraph X) (O:SimpleGraph Y)
    {s t r:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (row:ForcingRow (C⊕g O) s t (padDemand n) (padDemand m) r)
    (deficit:matchingEdges C+matchingEdges O<rowCount s t r) :
    s≤matchingEdges C ∨ t≤matchingEdges O := by
  by_contra! both
  let i := min r (s-matchingEdges C-1)
  let j := r-i
  have left : matchingEdges C<s-i := by dsimp [i];omega
  have right : matchingEdges O<t-j := by dsimp [j,i,rowCount] at *;omega
  have idx : i+j=r := by dsimp [i,j];omega
  have original := row i j (s-i) (t-j) idx (by omega) (by omega) (by omega) (by omega)
  have red : C≤C := le_rfl
  have blue : (⊥:SimpleGraph Y)≤O := bot_le
  obtain ⟨valid,comp⟩ := JSP452Audit.StarHost.sum_colors red blue
  rcases original _ valid with redCopy|blueCopy
  · have rank := forest_copy_matching _ (fun z:Fin (s-i) => padDemand n (i+z.val))
      (fun z => pad_positive n pn _ (by have := z.isLt;omega)) redCopy
    rw [matchingEdges_sumGraph,matchingEdges_bot,Fintype.card_fin] at rank;omega
  · rw [comp,sdiff_self,sdiff_bot] at blueCopy
    have rank := forest_copy_matching _ (fun z:Fin (t-j) => padDemand m (j+z.val))
      (fun z => pad_positive m pm _ (by have := z.isLt;omega)) blueCopy
    rw [matchingEdges_sumGraph,matchingEdges_bot,Fintype.card_fin] at rank;omega

theorem nine_port_pair_length_gap (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (nine:diagonal F.n F.m (F.r+2)-1=9) (R:NinePortRegion F.G) :
    let P := R.totalCapacity
    let d := F.rank-matchingEdges F.G-R.rankAllowance
    let r := F.r+R.roots.ncard
    (F.s≤P ∨ (F.t≤R.outsideRank ∧ P+r+d+1≤F.s)) ∧
      (F.t≤P ∨ (F.s≤R.outsideRank ∧ P+r+d+1≤F.t)) := by
  intro P d r
  let C := F.G.induce R.chosen
  let O := F.G.induce R.outside
  obtain ⟨positive,balance,row,_⟩ := strict_nine_root_deleted_row F paid nine R
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤9 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq nine
  have rank := (R.region_rank_edges cap).1
  change matchingEdges C=P at rank
  have fee : matchingEdges C+matchingEdges O<rowCount F.s F.t r := by
    change rowCount F.s F.t r=P+R.outsideRank+d at balance
    change 2≤d at positive;change matchingEdges C+R.outsideRank<_;omega
  have red := deficient_sum_row_length_dichotomy C O F.n F.m F.pn F.pm row fee
  have sw : rowCount F.t F.s r=rowCount F.s F.t r := by simp [rowCount,Nat.add_comm]
  have blue := deficient_sum_row_length_dichotomy C O F.m F.n F.pm F.pn (swap_positive_forcing_row _ _ _ row)
    (by rwa [sw])
  rw [rank] at red blue
  change F.s≤P ∨ F.t≤R.outsideRank at red
  change F.t≤P ∨ F.s≤R.outsideRank at blue
  change F.s+F.t-1-r=P+R.outsideRank+d at balance
  change 2≤d at positive
  omega

#print axioms deficient_sum_row_length_dichotomy
#print axioms nine_port_pair_length_gap
end JSP452Audit.StarHost
