import MissingWinningThreshold
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_source_missing_heights (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let μ := matchingEdges (F.G.induce K.core)
    (μ<F.s → MissingHeightWitness F.G K F.n F.m F.r) ∧
    (μ<F.t → MissingHeightWitness F.G K F.m F.n F.r) := by
  intro μ
  let D := diagonal F.n F.m (F.r+2)-1
  let d := F.rank-matchingEdges F.G
  have deg : 4≤D := strict_source_degree_at_least_four F paid
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have width := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).2
  obtain ⟨red,blue⟩ := strict_common_actual_successors F paid K
  constructor
  · intro esc
    exact actual_missing_height F.G K F.n F.m F.r F.rank d F.hs F.ht F.hn F.hm F.pn F.pm top
      (by omega) width rfl esc cap (red esc)
  · intro esc
    have data := blue esc
    rw [←row_energy_colour_swap F.m F.n] at data
    exact actual_missing_height F.G K F.m F.n F.r F.rank d F.ht F.hs F.hm F.hn F.pm F.pn
      ((diagonal_swap _ _ _).trans top) (by omega) ((highest_width_colour_swap _ _ _).le.trans width)
      (by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]) esc cap data

theorem missing_at_two_requires_longer_red_rectangle {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r : ℕ)
    (hs : 0<s) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (blue : 0<originalThresholdCount m 2) (some : ∃x y,WinsHeight n m r 2 x y)
    (missing : MissingAtHeight G K n m r 2) :
    s+originalThresholdCount m 2<originalThresholdCount n 2+t := by
  obtain ⟨x,y,win⟩ := some
  have nonunit := (missing _ _ win).1
  obtain ⟨_,py,height,_,_,area⟩ := win
  have pair : x=2 ∧ y=1 := by omega
  obtain ⟨rfl,rfl⟩ := pair
  rw [original_threshold_one m pm] at area
  have one := original_threshold_one n pn
  have red : 0<originalThresholdCount n 1 := by omega
  have other := actual_rectangle_le_column (r:=r) n m hn hm (a:=1) (b:=2) (h:=2) (by decide) red blue
  have ne : widthAt n m r 2 ≠ originalThresholdCount n 1+originalThresholdCount m 2-1-r := by
    intro eq
    have bad := (missing 1 2 ⟨by decide,by decide,by decide,red,blue,eq⟩).1
    omega
  omega

/-- Two escaping colors cannot both pay all heights from three upward:
at least one of their two actual joint accounts fails there. -/
theorem strict_double_escape_above_two (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1))
    (esc : matchingEdges (F.G.induce K.core)<min F.s F.t) :
    ∃j,3≤j ∧ j≤diagonal F.n F.m (F.r+2)-1 ∧
      ((UnpaidHeight F.G K F.n F.m F.r j ∧ MissingAtHeight F.G K F.n F.m F.r j) ∨
       (UnpaidHeight F.G K F.m F.n F.r j ∧ MissingAtHeight F.G K F.m F.n F.r j)) := by
  let D := diagonal F.n F.m (F.r+2)-1
  have large : 4≤D := strict_source_degree_at_least_four F paid
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  have live := F.live
  obtain ⟨i,j,_,peak⟩ := diagonal_attained F.n F.m F.hs F.ht F.r (by dsimp [rowCount] at live;omega)
  obtain ⟨nc,mc⟩ := minimal_original_head_cap F paid
  have na := nc i
  have mb := mc j
  have hi := (original_threshold_prefix F.n F.hn 2 i).1 (by omega)
  have hj := (original_threshold_prefix F.m F.hm 2 j).1 (by omega)
  obtain ⟨red,blue⟩ := strict_source_missing_heights F paid K
  obtain ⟨x,low,cap,ux,wx,mx⟩ := red ((lt_min_iff.mp esc).1)
  obtain ⟨y,low',cap',uy,wy,my⟩ := blue ((lt_min_iff.mp esc).2)
  by_cases above : 3≤x
  · exact ⟨x,above,cap,Or.inl ⟨ux,mx⟩⟩
  by_cases above' : 3≤y
  · exact ⟨y,above',cap',Or.inr ⟨uy,my⟩⟩
  obtain rfl : x=2 := by omega
  obtain rfl : y=2 := by omega
  have r := missing_at_two_requires_longer_red_rectangle F.G K F.n F.m F.r F.hs F.hn F.hm F.pn F.pm (by omega) wx mx
  have b := missing_at_two_requires_longer_red_rectangle F.G K F.m F.n F.r F.ht F.hm F.hn F.pm F.pn (by omega) wy my
  omega

#print axioms strict_source_missing_heights
#print axioms missing_at_two_requires_longer_red_rectangle
#print axioms strict_double_escape_above_two
end JSP452Audit.StarHost
