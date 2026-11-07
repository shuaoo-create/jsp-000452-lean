import ExposureOfActualStageExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem exact_typed_width_swap {X:Type*} (G:SimpleGraph X) {x y l:ℕ} (w:ExactTypedWidth G x y l) :
    ExactTypedWidth G y x l := by
  rcases w with zero|⟨u,v,hu,hv,eq,forces⟩
  · exact Or.inl zero
  · exact Or.inr ⟨v,u,hv,hu,by omega,forces_swap forces⟩

theorem typed_mono_sixth_winner {X:Type*} [Finite X] (G:SimpleGraph X) (T:Finset G.ConnectedComponent)
    {s t r x y L:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (rx:0<x) (byh:0<y)
    (blue:0<originalThresholdCount m y) (limit:originalThresholdCount m y≤r+1)
    (win:L=originalThresholdCount n x+originalThresholdCount m y-1-r)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) :
    ExactTypedWidth (G.induce (componentVertices G T)ᶜ) x y (L-chosenSlots G T x) := by
  let U := componentVertices G T
  let A := G.induce U
  let M := chosenSlots G T x
  change ExactTypedWidth _ x y (L-M)
  by_cases small : L≤M
  · exact Or.inl (by omega)
  have live : M<originalThresholdCount n x := by omega
  have residual := palette_retains_typed_rectangle (G.induce Uᶜ) A A le_rfl n m hn hm rx byh
    (selected_component_pack G T x rx) (by rw [sdiff_self];exact uniform_pack_bot_cap y byh) live blue
    (closed_union_sum_row G U (component_vertices_closed G T) row)
  simpa only [←win,Nat.sub_zero] using residual

theorem strict_single_six_no_five_typed (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (red:∀i,F.n i≤4) (blue:∀j,F.m j≤4)
    (T:Finset F.G.ConnectedComponent) :
    let O := F.G.induce (componentVertices F.G T)ᶜ
    let l := widthAt F.n F.m F.r 6-chosenSlots F.G T 3
    ExactTypedWidth O 3 4 l ∨ ExactTypedWidth O 4 3 l := by
  intro O l
  let L := widthAt F.n F.m F.r 6
  by_cases live:0<L
  · obtain ⟨x,y,rx,byh,height,rf,bg,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by decide : 0<6) live
    have nx := (original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 rf
    have my := (original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 bg
    have nr := red ⟨0,F.hs⟩
    have mb := blue ⟨0,F.ht⟩
    obtain ⟨n4,m4,_,_⟩ := six_degree_head_count_guards F paid six
    have h := (strict_six_only_one_original_component F paid six).1
    rw [h] at n4 m4
    have cases : (x=3 ∧ y=4) ∨ (x=4 ∧ y=3) := by omega
    rcases cases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact Or.inl (typed_mono_sixth_winner F.G T F.n F.m F.hn F.hm rx byh bg m4 win F.row)
    · right
      apply exact_typed_width_swap
      have eq := win.trans (by rw [Nat.add_comm (originalThresholdCount F.n 4)])
      exact typed_mono_sixth_winner F.G T F.m F.n F.hm F.hn byh rx rf n4 eq (swap_positive_forcing_row F.G _ _ F.row)
  · exact Or.inl (Or.inl (by change L-chosenSlots F.G T 3=0;omega))

#print axioms exact_typed_width_swap
#print axioms typed_mono_sixth_winner
#print axioms strict_single_six_no_five_typed
end JSP452Audit.StarHost
