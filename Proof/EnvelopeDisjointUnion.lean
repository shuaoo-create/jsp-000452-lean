import UniformPackSum
import EnvelopeReserve
import DegreeTwoSplit
import SumReserve
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit

namespace JSP452Audit.StarHost
open SimpleGraph

private theorem exists_uniform_avoidance {X : Type*} [Finite X] (G : SimpleGraph X)
    (a b r s h : ℕ) (ha : 0<a) (hb : 0<b) (height : a+b-1=h)
    (over : uniformEnvelope G h ≤ r+s) :
    ∃ R ≤ G, ¬(forest (fun _ : Fin (r+1) => a)).IsContained R ∧
      ¬(forest (fun _ : Fin (s+1) => b)).IsContained (G \ R) := by
  by_contra missing
  have force : Forces G (forest (fun _ : Fin (r+1) => a)) (forest (fun _ : Fin (s+1) => b)) := by
    intro R incl
    by_contra neither
    exact missing ⟨R,incl,fun r => neither (Or.inl r),fun b => neither (Or.inr b)⟩
  have := uniform_pair_le_envelope G a b (r+1) (s+1) h ha hb (by omega) (by omega) height force
  omega

/-- Allocate each side's whole envelope to its red and blue budgets.
The combined budgets are strictly smaller than their target multiplicities. -/
private theorem divide_budgets (left right p q : ℕ) (hp : 0<p) (hq : 0<q)
    (strict : left+right < p+q-1) :
    ∃ r₁ b₁ r₂ b₂ : ℕ, left = r₁+b₁ ∧ right = r₂+b₂ ∧ r₁+r₂ < p ∧ b₁+b₂ < q := by
  let r₁ := min left (p-1)
  let r₂ := min right (p-1-r₁)
  refine ⟨r₁,left-r₁,r₂,right-r₂,?_⟩
  dsimp [r₁,r₂]
  omega

/-- If a width exceeded the sum of the two envelopes, separate red/blue
avoidance colorings of both summands would give one avoidance coloring of
the entire disjoint sum. No component of a target star can cross the sum. -/
theorem uniformEnvelope_sum_le {X Y : Type*} [Finite X] [Finite Y]
    (G : SimpleGraph X) (H : SimpleGraph Y) (h : ℕ) :
    uniformEnvelope (G ⊕g H) h ≤ uniformEnvelope G h + uniformEnvelope H h := by
  by_contra! over
  obtain ⟨a,b,p,q,ha,hb,hp,hq,height,width,forces⟩ :=
    uniformEnvelope_attained (G ⊕g H) h (by omega)
  obtain ⟨r₁,b₁,r₂,b₂,left,right,redCap,blueCap⟩ :=
    divide_budgets (uniformEnvelope G h) (uniformEnvelope H h) p q hp hq (by omega)
  obtain ⟨R,rSub,rAvoid,bAvoid⟩ := exists_uniform_avoidance G a b r₁ b₁ h ha hb height left.le
  obtain ⟨S,sSub,sAvoid,tAvoid⟩ := exists_uniform_avoidance H a b r₂ b₂ h ha hb height right.le
  obtain ⟨sub,complement⟩ := JSP452Audit.StarHost.sum_colors rSub sSub
  rcases forces (R ⊕g S) sub with red | blue
  · have cap := uniform_copy_count_le_sum R S a r₁ r₂ rAvoid sAvoid p red
    omega
  · rw [complement] at blue
    have cap := uniform_copy_count_le_sum (G \ R) (H \ S) b b₁ b₂ bAvoid tAvoid q blue
    omega

/-- Actual reserves are superadditive because edge count and matching number
are exactly additive, while every uniform envelope is subadditive. -/
theorem envelopeReserve_superadditive {X Y : Type*} [Finite X] [Finite Y]
    (G : SimpleGraph X) (H : SimpleGraph Y) (D : ℕ) :
    envelopeReserve G D + envelopeReserve H D ≤ envelopeReserve (G ⊕g H) D := by
  have cost := Finset.sum_le_sum (s := Finset.range D)
    (fun j _ => uniformEnvelope_sum_le G H (j+2))
  rw [Finset.sum_add_distrib] at cost
  have joint := (envelope_reserve_account (G ⊕g H) D).1
  rw [matchingEdges_sumGraph,edge_ncard_sumGraph] at joint
  have left := (envelope_reserve_account G D).1
  have right := (envelope_reserve_account H D).1
  omega

#print axioms uniformEnvelope_sum_le
#print axioms envelopeReserve_superadditive
end JSP452Audit.StarHost
