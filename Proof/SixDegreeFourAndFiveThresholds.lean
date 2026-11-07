import ExactComponentUniformSlots
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem absent_rectangle_of_split {X:Type*} [Finite X] (G:SimpleGraph X) (P:SimpleGraph X) (sub:P≤G)
    {s t r x y:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (red:0<originalThresholdCount n x) (blue:0<originalThresholdCount m y)
    (capR:UniformPackCap P x 0) (capB:UniformPackCap (G \ P) y 0)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) :
    originalThresholdCount n x+originalThresholdCount m y≤r+1 := by
  let f := originalThresholdCount n x
  let g := originalThresholdCount m y
  change f+g≤r+1
  change 0<f at red
  change 0<g at blue
  by_contra! large
  let i := min r (f-1)
  let j := r-i
  have index : i+j=r := by dsimp [i,j];omega
  have fi : i<f := by dsimp [i];omega
  have gj : j<g := by dsimp [i,j];omega
  have force := uniform_rectangle_at G n m hn hm index fi gj row
  rcases force P sub with first|second
  · have := capR (f-i) first;omega
  · have := capB (g-j) second;omega

theorem six_degree_head_count_guards (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) :
    let h := highestWidth F.n F.m F.r
    originalThresholdCount F.n 4≤F.r+h ∧ originalThresholdCount F.m 4≤F.r+h ∧
      originalThresholdCount F.n 5≤F.r ∧ originalThresholdCount F.m 5≤F.r := by
  intro h
  obtain ⟨i,j,_,_,_,red,blue,_⟩ := strict_six_balanced_factor_cut F paid six
  have fr := (original_threshold_prefix F.n F.hn 4 i).mp red.ge
  have gb := (original_threshold_prefix F.m F.hm 4 j).mp blue.ge
  have threeR := (original_threshold_prefix F.n F.hn 3 i).mp (by omega)
  have threeB := (original_threshold_prefix F.m F.hm 3 j).mp (by omega)
  have cap := (minimal_rank_exact_source F paid).2.2.2.1
  have bound := actual_rectangle_le_column (r:=F.r) F.n F.m F.hn F.hm (a:=4) (b:=4) (h:=7) rfl
    (by omega) (by omega)
  have eq : widthAt F.n F.m F.r 7=h := by
    have top : diagonal F.n F.m (F.r+2)=7 := by omega
    rw [←top];exact width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm
  rw [eq] at bound
  have hpos := (strict_six_real_component_bounds F paid six).1
  change 1≤h at hpos
  obtain ⟨R,sub,split⟩ := even_even_degree_split F.G 1 2 (fun v => (cap v).trans_eq six)
  have noneR := uniform_pack_below_degree R 3 (fun v => (split v).1.trans_lt (by decide))
  have noneB := uniform_pack_below_degree (F.G \ R) 5 (fun v => (split v).2.trans_lt (by decide))
  obtain ⟨B,bsub,swap⟩ := even_even_degree_split F.G 2 1 (fun v => (cap v).trans_eq six)
  have absentR := uniform_pack_below_degree B 5 (fun v => (swap v).1.trans_lt (by decide))
  have absentB := uniform_pack_below_degree (F.G \ B) 3 (fun v => (swap v).2.trans_lt (by decide))
  refine ⟨by omega,by omega,?_,?_⟩
  · by_cases live : 0<originalThresholdCount F.n 5
    · have := absent_rectangle_of_split F.G B bsub F.n F.m F.hn F.hm live (by omega) absentR absentB F.row;omega
    · omega
  · by_cases live : 0<originalThresholdCount F.m 5
    · have := absent_rectangle_of_split F.G R sub F.n F.m F.hn F.hm (by omega) live noneR noneB F.row;omega
    · omega

#print axioms absent_rectangle_of_split
#print axioms six_degree_head_count_guards
end JSP452Audit.StarHost
