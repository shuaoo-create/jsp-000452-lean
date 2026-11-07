import LastSixStageEqualities
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem last_six_winner_two_five (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (c:F.G.ConnectedComponent) (mem:c∈oddRegularComponents F.G 6) :
    WinsHeight F.n F.m F.r 6 2 5 ∨ WinsHeight F.n F.m F.r 6 5 2 := by
  obtain ⟨B,out⟩ := complete_degree_stage_exists (F.G.induce c.suppᶜ) 6
  obtain ⟨A,_,_,stage,left,exposure,_⟩ := last_six_residual_certificate F paid six c mem B out
  let S := Subtype.val '' A∪Subtype.val '' B
  let L := widthAt F.n F.m F.r 6
  change S.ncard+4=L at left
  change minimumExposure (F.G.induce Sᶜ) 5=4 at exposure
  have cap (v:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq six
  have low (v) : Nat.card ((F.G.induce Sᶜ).neighborSet v)≤5 := by have := complete_stage_lowers_cap F.G 6 S cap stage v;omega
  obtain ⟨x,y,rx,byh,ht,rf,bg,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (by decide : 0<6) (show 0<L by omega)
  have nhead := (original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 rf
  have mhead := (original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 bg
  have bounds := strict_only_double_escape F paid
  have nx := bounds.1 ⟨0,F.hs⟩
  have my := bounds.2.1 ⟨0,F.ht⟩
  rw [six] at nx my
  have typed := typed_width_of_original_rectangle F.G F.n F.m F.hn F.hm rf bg F.row
  rw [←win] at typed
  have remaining := typed_width_after_deletion F.G S rx byh typed
  change ExactTypedWidth (F.G.induce Sᶜ) x y (L-S.ncard) at remaining
  have four : L-S.ncard=4 := by omega
  rw [four] at remaining
  have cases : (x=2 ∧ y=5) ∨ (x=5 ∧ y=2) ∨ (x=3 ∧ y=4) ∨ (x=4 ∧ y=3) := by omega
  rcases cases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inl ⟨rx,byh,ht,rf,bg,win⟩
  · exact Or.inr ⟨rx,byh,ht,rf,bg,win⟩
  · have impossible := sharp_five_from_typed_width (F.G.induce Sᶜ) low 4 (Or.inr remaining)
    omega
  · have impossible := sharp_five_from_typed_width (F.G.induce Sᶜ) low 4 (Or.inl remaining)
    omega

theorem typed_five_exposure_floor {X:Type*} [Finite X] (G:SimpleGraph X) (cap:∀v,Nat.card (G.neighborSet v)≤5)
    {x y l:ℕ} (xp:0<x) (yp:0<y) (height:x+y-1=6) (typed:ExactTypedWidth G x y l) :
    l≤minimumExposure G 5 := by
  rcases typed with zero|⟨u,v,up,vp,wide,force⟩
  · omega
  · have actual := uniform_pair_le_envelope G x y u v 6 xp yp up vp height force
    rw [wide] at actual
    exact actual.trans ((uniformEnvelope_le_deletion G 5 (by decide)).trans (deletionBudget_le_minimumExposure G 5 (by decide) cap))

#print axioms last_six_winner_two_five
#print axioms typed_five_exposure_floor
end JSP452Audit.StarHost
