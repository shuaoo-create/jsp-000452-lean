import OriginalStrictDegreeTenExcluded
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Choose a winning pair at the last interior column that minimizes the
smaller head amongst all actual winners, keeping both original labels. -/
theorem minimum_head_at_last_interior_column (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let gap := D-H
    ∃a b, WinsHeight F.n F.m F.r D a b ∧ gap+1≤min a b ∧ max a b≤H ∧
      (∀x y,WinsHeight F.n F.m F.r D x y → min a b≤min x y) := by
  classical
  intro D H gap
  have low : 11≤D := strict_source_degree_at_least_eleven F paid
  have actual : 0<widthAt F.n F.m F.r D :=
    (width_positive_at_first_offset F.hs F.ht F.n F.m F.hn F.hm).mpr ⟨F.live,by dsimp only [D];omega⟩
  obtain ⟨x,y,xp,yp,ht,red,blue,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by omega : 0<D) actual
  let eligible (k:ℕ) := ∃a b,WinsHeight F.n F.m F.r D a b ∧ min a b=k
  have existsK : ∃k,eligible k := ⟨min x y,x,y,⟨xp,yp,ht,red,blue,w⟩,rfl⟩
  obtain ⟨a,b,win,least⟩ := Nat.find_spec existsK
  have ha := (original_threshold_prefix F.n F.hn a ⟨0,F.hs⟩).2 win.2.2.2.1
  have hb := (original_threshold_prefix F.m F.hm b ⟨0,F.ht⟩).2 win.2.2.2.2.1
  have size := win.2.2.1
  have pos := win.1
  have live := win.2.1
  refine ⟨a,b,win,by dsimp only [gap,H];omega,by dsimp only [H];omega,?_⟩
  intro x y winner
  rw [least];exact Nat.find_min' existsK (show eligible (min x y) from ⟨x,y,winner,rfl⟩)

theorem strict_high_source_domains (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let gap := D-H
    11≤D ∧ ActualPeakObstruction F ∧ gap+2≤min (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩) ∧
      ((8≤gap) ∨ (2≤gap ∧ gap≤7) ∨ (gap=1 ∧ (D=11 ∨ D=12)) ∨
        (gap=1 ∧ 13≤D ∧ ∃a b,WinsHeight F.n F.m F.r D a b ∧
          (min a b=2 ∨ min a b=3 ∨ (4≤min a b ∧ ∀x y,WinsHeight F.n F.m F.r D x y → 4≤min x y)))) := by
  intro D H gap
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  obtain ⟨pos,_,heads,limits⟩ := strict_double_head_gap_range F paid
  change 1≤gap at pos
  change gap+2≤_ at heads
  refine ⟨deg,strict_actual_peak_factor_obstruction F paid,heads,?_⟩
  by_cases high:8≤gap
  · exact Or.inl high
  by_cases middle:2≤gap
  · exact Or.inr (Or.inl ⟨middle,by omega⟩)
  by_cases low:D≤12
  · exact Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))
  obtain ⟨a,b,win,floor,_,minimize⟩ := minimum_head_at_last_interior_column F paid
  change gap+1≤min a b at floor
  refine Or.inr (Or.inr (Or.inr ⟨by omega,by omega,a,b,win,?_⟩))
  by_cases pair:min a b≤3
  · omega
  · exact Or.inr (Or.inr ⟨by omega,fun x y won => (by omega : 4≤min a b).trans (minimize x y won)⟩)

#print axioms minimum_head_at_last_interior_column
#print axioms strict_high_source_domains
end JSP452Audit.StarHost
