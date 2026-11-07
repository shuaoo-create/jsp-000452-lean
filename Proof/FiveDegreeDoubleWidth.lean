import FiveBlueRestoration
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X : Type*} [Finite X]

theorem four_three_double_width (G : SimpleGraph X) (cap : ∀x,Nat.card (G.neighborSet x)≤5)
    (p q : ℕ) (hp : 0<p) (hq : 0<q)
    (forced : Forces G (forest (fun _ : Fin p => 4)) (forest (fun _ : Fin q => 3))) :
    2*(p+q-1)≤minimumExposure G 5 := by
  classical
  obtain ⟨s⟩ := five_exposure_ports_exist G
  let J := (⊥ : SimpleGraph (s.U⊕Empty))
  let H := s.auxiliary J
  have upper (v:X⊕(s.U⊕Empty)) : Nat.card (H.neighborSet v)≤4 := by
    rcases v with x|u|z
    · exact s.old_port_degree_cap J cap x
    · rw [s.port_degree];simp [J]
    · exact z.elim
  obtain ⟨R,sub,caps⟩ := even_even_degree_split H 1 1 upper
  obtain ⟨a,b⟩ := s.both_port_colours_pay J R sub caps p q hp hq forced
  have total := Set.ncard_add_ncard_compl (s.marked R)
  rw [Nat.card_coe_set_eq,s.count] at total
  omega

/-- With uniform four-versus-three demand on a true strict source, the only
surviving arithmetic case has one star of each size and two exposed labels. -/
theorem five_degree_subcap_reduces_to_two_ports (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (five : diagonal F.n F.m (F.r+2)-1=5) (red : F.n ⟨0,F.hs⟩<5) (blue : F.m ⟨0,F.ht⟩<5) :
    highestWidth F.n F.m F.r=1 ∧ minimumExposure F.G 5=2 ∧
      Forces F.G (forest (fun _ : Fin 1 => 4)) (forest (fun _ : Fin 1 => 3)) := by
  obtain ⟨p,q,hp,hq,charge,force,cap,_,_⟩ := five_degree_small_heads_frontier F paid five red blue
  obtain ⟨pos,_,bound,_,_⟩ := five_degree_strict_exposure_bounds F paid five
  have lower := four_three_double_width F.G cap p q hp hq force
  have width : highestWidth F.n F.m F.r=1 := by omega
  have pi : p=1 := by omega
  have qi : q=1 := by omega
  subst p;subst q
  exact ⟨width,by omega,force⟩

#print axioms four_three_double_width
#print axioms five_degree_subcap_reduces_to_two_ports
end JSP452Audit.StarHost
