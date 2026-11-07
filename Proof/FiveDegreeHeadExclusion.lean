import FivePairedPortCut
import RootDeletionCost
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X : Type*} [Finite X]

/-- With exactly two exposed labels, the two auxiliary port edges must have
the same color. Both positive uniform forests cannot then be forced. -/
theorem two_exposed_labels_preclude_four_three (G : SimpleGraph X) (cap : ∀v,Nat.card (G.neighborSet v)≤5)
    (two : minimumExposure G 5=2) (p q : ℕ) (hp : 0<p) (hq : 0<q)
    (forced : Forces G (forest (fun _ : Fin p => 4)) (forest (fun _ : Fin q => 3))) : False := by
  classical
  obtain ⟨s⟩ := five_exposure_ports_exist G
  have size : Nat.card s.U=2 := by rw [Nat.card_coe_set_eq,s.count,two]
  let J := two_port_piece s.U
  let H := s.auxiliary J
  let K := s.addedSet (Z:=Fin 3)
  have full (y : s.U⊕Fin 3) : Nat.card (H.neighborSet (.inr y))=4 := by
    rcases y with u|z
    · rw [s.port_degree,two_port_piece_label_degree]
    · rw [s.extra_degree,two_port_piece_internal_degree size]
  have upper (v : X⊕(s.U⊕Fin 3)) : Nat.card (H.neighborSet v)≤4 := by
    rcases v with x|y
    · exact s.old_port_degree_cap J cap x
    · exact (full y).le
  obtain ⟨R,sub,caps⟩ := even_even_degree_split H 1 1 upper
  obtain ⟨left,right⟩ := s.both_port_colours_pay J R sub caps p q hp hq forced
  have total := Set.ncard_add_ncard_compl (s.marked R)
  rw [size] at total
  have cut : crossCount R K Kᶜ=1 := by rw [s.red_port_cross_count J R sub];omega
  have dis : Disjoint R (H \ R) := SimpleGraph.disjoint_left.mpr (fun _ _ h e => e.2 h)
  have redDegree (v : X⊕(s.U⊕Fin 3)) (hv:v∈K) : Nat.card (R.neighborSet v)=2 := by
    obtain ⟨y,rfl⟩ := hv
    have sum := neighbor_card_sup_of_disjoint dis (Sum.inr y)
    rw [sup_sdiff_cancel_right sub,full y] at sum
    obtain ⟨a,b⟩ := caps (Sum.inr y)
    change Nat.card (R.neighborSet (Sum.inr y))≤2 at a
    change Nat.card ((H \ R).neighborSet (Sum.inr y))≤2 at b
    omega
  have parity := JSP452Audit.StarHost.two_block_handshake R K
  rw [degree_sum_full R K 2 redDegree,cut] at parity
  omega

theorem five_degree_requires_original_full_head (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (five : diagonal F.n F.m (F.r+2)-1=5) :
    F.n ⟨0,F.hs⟩=5 ∨ F.m ⟨0,F.ht⟩=5 := by
  obtain ⟨nc,mc⟩ := minimal_original_head_cap F paid
  rw [five] at nc mc
  by_contra! below
  have n5 := lt_of_le_of_ne (nc ⟨0,F.hs⟩) below.1
  have m5 := lt_of_le_of_ne (mc ⟨0,F.ht⟩) below.2
  obtain ⟨_,two,force⟩ := five_degree_subcap_reduces_to_two_ports F paid five n5 m5
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  rw [five] at cap
  exact two_exposed_labels_preclude_four_three F.G cap two 1 1 (by decide) (by decide) force

/-- No minimal strict source of degree three through five can have both
original heads below the cap, independently of its region embedding type. -/
theorem minimal_subcap_heads_force_degree_six (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    F.n ⟨0,F.hs⟩<D → F.m ⟨0,F.ht⟩<D → 6≤D := by
  intro D red blue
  by_contra! small
  by_cases low : D≤4
  · rcases low_degree_forces_head_at_cap F paid low with r|b <;> omega
  have five : D=5 := by omega
  rcases five_degree_requires_original_full_head F paid five with r|b <;> omega

#print axioms two_exposed_labels_preclude_four_three
#print axioms five_degree_requires_original_full_head
#print axioms minimal_subcap_heads_force_degree_six
end JSP452Audit.StarHost
