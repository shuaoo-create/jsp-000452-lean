import StrictSourceClassificationBridge
import RegionForcing
import DegreeTwoSplit
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit

namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Test the extreme admissible index whose red suffix still exceeds A.
The resulting blue suffix forces B to cover all t original blue stars. -/
private theorem fd_length_from_choices {s t r A B d : ℕ} (ht : 0<t)
    (small : A<s) (pos : 0<d) (account : A+B+d=rowCount s t r)
    (choices : ∀i j, i<s → j<t → i+j=r → s-i≤A ∨ t-j≤B) :
    A+r+d+1≤s ∧ t≤B := by
  let i := min r (s-1-A)
  let j := r-i
  dsimp [rowCount] at account
  have hi : i<s := by dsimp [i]; omega
  have hj : j<t := by dsimp [j,i]; omega
  have index : i+j=r := by dsimp [j,i]; omega
  rcases choices i j hi hj index with red|blue
  · dsimp [i] at red; omega
  · dsimp [j,i] at blue; omega

private theorem fd_rank_choices {X : Type*} [Finite X] (G : SimpleGraph X)
    {s t r : ℕ} (n m : ℕ→ℕ) (pn : ∀i<s, 0<n i) (pm : ∀j<t, 0<m j)
    (row : ForcingRow G s t n m r) (R : SimpleGraph X) (sub : R≤G)
    (i j : ℕ) (hi : i<s) (hj : j<t) (index : i+j=r) :
    s-i≤matchingEdges R ∨ t-j≤matchingEdges (G \ R) := by
  have force := row i j (s-i) (t-j) index (by omega) (by omega) (by omega) (by omega)
  rcases force R sub with red|blue
  · left
    have bound := forest_copy_matching R (fun a : Fin (s-i) => n (i+a.val))
      (fun a => pn _ (by have := a.isLt; omega)) red
    simpa only [Fintype.card_fin] using bound
  · right
    have bound := forest_copy_matching (G \ R) (fun b : Fin (t-j) => m (j+b.val))
      (fun b => pm _ (by have := b.isLt; omega)) blue
    simpa only [Fintype.card_fin] using bound

/-- Both orientations of the same coloring give the strong list lengths.
A and B are the actual matching ranks of the two color graphs. -/
theorem forcing_row_strong_lengths_of_coloring {X : Type*} [Finite X]
    (G : SimpleGraph X) {s t r : ℕ} (hs : 0<s) (ht : 0<t)
    (n m : ℕ→ℕ) (pn : ∀i<s, 0<n i) (pm : ∀j<t, 0<m j)
    (row : ForcingRow G s t n m r) (R : SimpleGraph X) (sub : R≤G)
    (d : ℕ) (pos : 0<d)
    (account : matchingEdges R+matchingEdges (G \ R)+d=rowCount s t r)
    (small : matchingEdges R<min s t) :
    matchingEdges R+r+d+1≤min s t ∧ max s t≤matchingEdges (G \ R) := by
  have red := fd_length_from_choices ht (lt_min_iff.mp small).1 pos account
    (fd_rank_choices G n m pn pm row R sub)
  have inv : G \ (G \ R)=R := by
    ext x y
    simp only [sdiff_adj]
    have contained : R.Adj x y → G.Adj x y := fun h => sub h
    tauto
  have rev (i j : ℕ) (hi : i<t) (hj : j<s) (index : i+j=r) :
      t-i≤matchingEdges R ∨ s-j≤matchingEdges (G \ R) := by
    have choice := fd_rank_choices G n m pn pm row (G \ R) sdiff_le j i hj hi (by omega)
    rw [inv] at choice
    exact choice.symm
  have swapped : matchingEdges R+matchingEdges (G \ R)+d=rowCount t s r := by
    simpa only [rowCount, Nat.add_comm t s] using account
  have blue := fd_length_from_choices hs (lt_min_iff.mp small).2 pos swapped rev
  exact ⟨le_min red.1 blue.1,max_le blue.2 red.2⟩

/-- An arbitrary strict source already bounds both *original* list lengths
by the complete matching deficit, even without any regular-component price. -/
theorem strict_source_strong_lengths (F : StrictFamily.{u}) :
    F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t ∧ max F.s F.t≤matchingEdges F.G := by
  have cost := row_energy_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row
  have strict := F.strict
  have deficit : matchingEdges F.G<F.rank := by change _<rowCount F.s F.t F.r; omega
  let R := (⊥ : SimpleGraph F.X)
  have first : matchingEdges R=0 := matchingEdges_bot
  have other : F.G \ R=F.G := sdiff_bot
  have bounds := forcing_row_strong_lengths_of_coloring F.G F.hs F.ht
    (padDemand F.n) (padDemand F.m) (pad_positive F.n F.pn) (pad_positive F.m F.pm)
    F.row R bot_le (F.rank-matchingEdges F.G) (by omega)
    (by rw [first,other]; change 0+matchingEdges F.G+(F.rank-matchingEdges F.G)=F.rank; omega)
    (by rw [first]; exact lt_min F.hs F.ht)
  simpa only [first,other,Nat.zero_add] using bounds

/-- Delete the actual roots, keep the original lists, and color all core edges
one color and all rest edges the other. A positive global rank deficit is
preserved exactly. The alternative displays the outstanding core-rank gate. -/
theorem strict_source_region_length_alternative (F : StrictFamily.{u}) {D : ℕ}
    (K : DegreeRegion F.G D) :
    let μ := matchingEdges (F.G.induce K.core)
    let d := F.rank-matchingEdges F.G
    min F.s F.t≤μ ∨
      (μ+K.roots.ncard+F.r+d+1≤min F.s F.t ∧
       max F.s F.t≤matchingEdges (F.G.induce K.rest)) := by
  intro μ d
  by_cases small : μ<min F.s F.t
  · right
    let C := F.G.induce K.core
    let B := F.G.induce K.rest
    let H := C ⊕g B
    let R := C ⊕g (⊥ : SimpleGraph K.rest)
    have rankPartition := region_rank_partition F.G K.barrier K.tight K.pieces
    change matchingEdges F.G=K.roots.ncard+matchingEdges C+matchingEdges B at rankPartition
    have cost := row_energy_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row
    have strict := F.strict
    have deficit : matchingEdges F.G<F.rank := by change _<rowCount F.s F.t F.r; omega
    have dpos : 0<d := by dsimp [d]; omega
    have rootRow := row_delete_set F.G K.roots _ _ (pad_antitone F.n F.hn)
      (pad_antitone F.m F.hm) (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row
    obtain ⟨cover,apart,separate⟩ := core_rest_partition F.G K.barrier K.pieces
    let iso := regionSumIso F.G K.rootsᶜ K.core K.rest cover apart
      (fun _ hx _ hy => separate hx hy)
    have rowSum := forcingRow_of_iso iso.symm rootRow
    obtain ⟨sub,complement⟩ := JSP452Audit.StarHost.sum_colors (le_refl C)
      (bot_le : (⊥ : SimpleGraph K.rest)≤B)
    have redRank : matchingEdges R=μ := by
      dsimp [R]; rw [matchingEdges_sumGraph,matchingEdges_bot,Nat.add_zero]
    have blueRank : matchingEdges (H \ R)=matchingEdges B := by
      change matchingEdges ((C ⊕g B) \ (C ⊕g ⊥))=matchingEdges B
      rw [complement,sdiff_self,sdiff_bot,matchingEdges_sumGraph,matchingEdges_bot,Nat.zero_add]
    have account : matchingEdges R+matchingEdges (H \ R)+d=rowCount F.s F.t (F.r+K.roots.ncard) := by
      rw [redRank,blueRank]
      change matchingEdges C+matchingEdges B+(F.rank-matchingEdges F.G)=_
      change matchingEdges F.G<rowCount F.s F.t F.r at deficit
      dsimp [StrictFamily.rank,rowCount] at deficit ⊢
      omega
    have paid := forcing_row_strong_lengths_of_coloring H F.hs F.ht
      (padDemand F.n) (padDemand F.m) (pad_positive F.n F.pn) (pad_positive F.m F.pm)
      rowSum R sub d dpos account (redRank ▸ small)
    rw [redRank,blueRank] at paid
    exact ⟨by omega,paid.2⟩
  · exact Or.inl (Nat.le_of_not_gt small)

/-- The literal original entry equality when either original target consists
of a single arbitrary positive star, with arbitrary positive opposite list. -/
theorem erdos561_single_list {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (short : min s t=1) :
    sizeRamsey (forest n) (forest m)=∑ k∈Finset.Icc 2 (s+t),diagonal n m k := by
  obtain ⟨V,G,edges,forced⟩ := star_min_attained n m
  have upper := erdos561_upper n m
  have row := (finite_targets_row_zero G hs ht n m).mpr forced
  have paid : rowEnergy n m 0≤G.edgeSet.ncard := by
    by_contra! un
    have limits := strict_row_range hs ht n m hn hm pn pm G 0 row un
    omega
  rw [edges,rowEnergy_zero] at paid
  exact le_antisymm upper paid

/-- Starting from failure of the full original formula, the stronger
constraints apply to the very same globally minimal source and every
actual degree region of its critical height. -/
theorem original_failure_region_strong_lengths {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑ k∈Finset.Icc 2 (s+t),diagonal n m k) :
    ∃ F : StrictFamily.{u}, AllSmallerPaid.{u} F.rank ∧
      (∀ B : StrictFamily.{u}, B.rank=F.rank → F.edges≤B.edges) ∧
      (∀ B : StrictFamily.{u}, B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧
      (F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t ∧ max F.s F.t≤matchingEdges F.G) ∧
      ∀ K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1),
        let μ := matchingEdges (F.G.induce K.core)
        min F.s F.t≤μ ∨ (μ+K.roots.ncard+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t ∧
          max F.s F.t≤matchingEdges (F.G.induce K.rest)) := by
  obtain ⟨F,paid,edges,order⟩ := failure_has_smaller_rank_baseline.{u} hs ht n m hn hm pn pm fail
  exact ⟨F,paid,edges,order,strict_source_strong_lengths F,
    fun K => strict_source_region_length_alternative F K⟩

#print axioms forcing_row_strong_lengths_of_coloring
#print axioms strict_source_strong_lengths
#print axioms strict_source_region_length_alternative
#print axioms erdos561_single_list
#print axioms original_failure_region_strong_lengths
end JSP452Audit.StarHost

