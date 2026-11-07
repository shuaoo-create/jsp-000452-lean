import StrictSingleEscapeUnpaidTypes
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- With a full red head, a positive blue two-leaf prefix fits under the
original top width. The actual exterior has a longer red suffix than
that whole blue prefix. -/
theorem full_head_blocks_internal_mixed {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r d j x y : ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i)
    (head : n ⟨0,hs⟩=D) (top : diagonal n m (r+2)=D+1)
    (width : highestWidth n m r≤minimumExposure G D) (reserve : minimumExposure G D+1≤d)
    (ext : r+2*d≤s-matchingEdges (G.induce K.core))
    (esc : matchingEdges (G.induce K.core)<s)
    (kinds : SingleUnpaidKinds G K n m ht r) (loss : UnpaidHeight G K n m r j)
    (win : WinsHeight n m r j x y) :
    (y=1 ∧ x=j) ∨ (x=2 ∧ y=m ⟨0,ht⟩ ∧ j=m ⟨0,ht⟩+1) := by
  rcases kinds j x y loss win with pure|⟨two,_,cases⟩
  · exact Or.inl pure
  rcases cases with ⟨twoB,three⟩|bound
  · subst x;subst y;subst j
    have P : 0<originalThresholdCount n D := (original_threshold_prefix n hn D ⟨0,hs⟩).1 head.ge
    have Bpos := win.2.2.2.2.1
    have rect := actual_rectangle_le_column (r:=r) n m hn hm (a:=D) (b:=2) (h:=D+1)
      (by omega) P Bpos
    have high := width_at_actual_top (r:=r) hs ht n m hn hm
    rw [top] at high
    rw [high] at rect
    have gSmall : originalThresholdCount m 2<s-matchingEdges (G.induce K.core) := by omega
    obtain ⟨_,_,limited,_⟩ := unpaid_height_missing_threshold G K n m r 3 hn hm pn esc loss 2 2 win
    have born := (original_threshold_prefix m hm 2 ⟨0,ht⟩).2 Bpos
    have value : m ⟨0,ht⟩=2 := by
      by_contra! ne
      have present := (original_threshold_prefix m hm 3 ⟨0,ht⟩).1 (by omega)
      have red : 0<originalThresholdCount n 1 := by rw [original_threshold_one n pn];exact hs
      have blue := actual_rectangle_le_column (r:=r) n m hn hm (a:=1) (b:=3) (h:=3) (by decide) red present
      rw [original_threshold_one n pn] at blue
      have eq := win.2.2.2.2.2
      have strict := loss
      unfold UnpaidHeight at strict
      have live : 0<widthAt n m r 3 := by omega
      omega
    exact Or.inr ⟨rfl,value.symm,by omega⟩
  · exact Or.inr ⟨two,bound⟩

theorem strict_full_head_unpaid_boundary (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    (F.n ⟨0,F.hs⟩=D → ∀j x y,UnpaidHeight F.G K F.n F.m F.r j → WinsHeight F.n F.m F.r j x y →
      (y=1 ∧ x=j) ∨ (x=2 ∧ y=F.m ⟨0,F.ht⟩ ∧ j=F.m ⟨0,F.ht⟩+1)) ∧
    (F.m ⟨0,F.ht⟩=D → ∀j x y,UnpaidHeight F.G K F.m F.n F.r j → WinsHeight F.m F.n F.r j x y →
      (y=1 ∧ x=j) ∨ (x=2 ∧ y=F.n ⟨0,F.hs⟩ ∧ j=F.n ⟨0,F.hs⟩+1)) := by
  intro D
  let μ := matchingEdges (F.G.induce K.core)
  let d := F.rank-matchingEdges F.G
  have deg : 4≤D := strict_source_degree_at_least_four F paid
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have w := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).2
  have reserve := (minimal_strict_source_deficit F paid).2.1
  have unique := strict_full_head_unique_escape F paid K
  have kinds := strict_single_unpaid_types F paid K
  have guard := strict_exterior_endpoint_guards F paid K
  constructor
  · intro head j x y loss win
    obtain ⟨inner,len,_,_⟩ := unique.1 head
    change μ+K.roots.ncard+F.r+d+1≤F.s at len
    have esc : μ<F.s := by omega
    have outer := guard.1 esc
    change K.roots.ncard+F.r+2*(d+_)+_≤F.s-μ at outer
    exact full_head_blocks_internal_mixed F.G K F.n F.m F.r d j x y F.hs F.ht F.hn F.hm F.pn head
      top w reserve (by change F.r+2*d≤F.s-μ;omega) esc (kinds.1 esc inner) loss win
  · intro head j x y loss win
    obtain ⟨inner,len,_,_⟩ := unique.2 head
    change μ+K.roots.ncard+F.r+d+1≤F.t at len
    have esc : μ<F.t := by omega
    have outer := guard.2 esc
    change K.roots.ncard+F.r+2*(d+_)+_≤F.t-μ at outer
    exact full_head_blocks_internal_mixed F.G K F.m F.n F.r d j x y F.ht F.hs F.hm F.hn F.pm head
      ((diagonal_swap _ _ _).trans top) ((highest_width_colour_swap _ _ _).le.trans w) reserve
      (by change F.r+2*d≤F.t-μ;omega) esc (kinds.2 esc inner) loss win

#print axioms full_head_blocks_internal_mixed
#print axioms strict_full_head_unpaid_boundary
end JSP452Audit.StarHost
