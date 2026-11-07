import EnvelopeReserve
import UniformSubforest
namespace JSP452Audit.StarHost
open SimpleGraph

private theorem forced_uniform_order {X : Type*} [Finite X] (G : SimpleGraph X) (a b p q : ℕ)
    (hb : 0<b) (hq : 0<q)
    (f : Forces G (forest (fun _ : Fin p => a)) (forest (fun _ : Fin q => b))) :
    p*(a+1) ≤ Nat.card X := by
  have live : (forest (fun _ : Fin p => a)).IsContained G := by
    rcases f G le_rfl with hr | hc
    · exact hr
    · obtain ⟨c⟩ := hc
      let w := center (fun _ : Fin q => b) ⟨0,hq⟩
      obtain ⟨l,adj⟩ := forest_has_neighbor (fun _ : Fin q => b) (fun _ => hb) w
      have edge := c.toHom.map_adj adj
      exact (edge.2 edge.1).elim
  obtain ⟨c⟩ := live
  have cmp := Nat.card_le_card_of_injective c c.injective
  change Nat.card (Σ _ : Fin p, Fin (a+1)) ≤ Nat.card X at cmp
  simpa [Nat.card_sigma] using cmp

theorem envelope_two_vertex_bound {X : Type*} [Finite X] (G : SimpleGraph X) :
    uniformEnvelope G 2 ≤ Nat.card X/2 + Nat.card X/3-1 := by
  by_cases pos : 0<uniformEnvelope G 2
  · obtain ⟨a,b,p,q,ha,hb,hp,hq,height,w,force⟩ := uniformEnvelope_attained G 2 pos
    have red := forced_uniform_order G a b p q hb hq force
    have blue := forced_uniform_order G b a q p ha hp (forces_swap force)
    have sides : a=1 ∧ b=2 ∨ a=2 ∧ b=1 := by omega
    rcases sides with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega
  · omega

/-- Slack from the first deletion layer appears in the actual reserve once
that layer is included. Each of the other layers contributes nonnegatively. -/
theorem envelope_first_gain {X : Type*} [Finite X] (G : SimpleGraph X) (k : ℕ) :
    baseReserve G (k+1) + deletionBudget G 1 ≤ envelopeReserve G (k+1) + uniformEnvelope G 2 := by
  have cut := base_reserve_account G (k+1)
  have env := (envelope_reserve_account G (k+1)).1
  rw [Finset.sum_range_succ'] at cut env
  simp only [Nat.zero_add] at cut env
  have other := Finset.sum_le_sum (s:=Finset.range k)
    (fun i _ => uniformEnvelope_le_deletion G (i+1+1) (by omega))
  change (∑i∈Finset.range k,uniformEnvelope G ((i+1)+2)) ≤ ∑i∈Finset.range k,deletionBudget G ((i+1)+1) at other
  omega
#print axioms envelope_two_vertex_bound
#print axioms envelope_first_gain
end JSP452Audit.StarHost