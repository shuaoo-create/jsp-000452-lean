import ColumnDeletion
import PackingFloor

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*} [Finite X]

/-- Width w is witnessed by two nonempty uniform forests genuinely forced on
the same host, with positive leaf counts and the required height. -/
def UniformWidthWitness (G : SimpleGraph X) (h w : ℕ) : Prop :=
  ∃ a b p q : ℕ, 0<a ∧ 0<b ∧ 0<p ∧ 0<q ∧ a+b-1=h ∧ p+q-1=w ∧
    Forces G (forest (fun _ : Fin p => a)) (forest (fun _ : Fin q => b))

/-- All-red and all-blue imply both multiplicities are bounded by the
ordinary matching number, giving a finite search interval for widths. -/
private theorem witness_bounded (G : SimpleGraph X) {h w : ℕ} (hw : UniformWidthWitness G h w) :
    w ≤ 2*matchingEdges G := by
  obtain ⟨a,b,p,q,ha,hb,hp,hq,_,rfl,forces⟩ := hw
  have both := forcing_matching_floor hp hq (fun _ : Fin p => a) (fun _ : Fin q => b)
    (fun _ => ha) (fun _ => hb) G forces
  have pair := max_le_iff.mp both
  omega

/-- The largest actually forced width at this height, with zero when the
height admits no pair. No assertion about the first height is built in. -/
noncomputable def uniformEnvelope {V : Type*} [Finite V] (G : SimpleGraph V) (h : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (UniformWidthWitness G h) (2*matchingEdges G)

theorem uniform_pair_le_envelope (G : SimpleGraph X) (a b p q h : ℕ)
    (ha : 0<a) (hb : 0<b) (hp : 0<p) (hq : 0<q) (height : a+b-1=h)
    (forces : Forces G (forest (fun _ : Fin p => a)) (forest (fun _ : Fin q => b))) :
    p+q-1 ≤ uniformEnvelope G h := by
  classical
  have w : UniformWidthWitness G h (p+q-1) := ⟨a,b,p,q,ha,hb,hp,hq,height,rfl,forces⟩
  exact Nat.le_findGreatest (witness_bounded G w) w

theorem uniformEnvelope_attained (G : SimpleGraph X) (h : ℕ) (pos : 0<uniformEnvelope G h) :
    ∃ a b p q : ℕ, 0<a ∧ 0<b ∧ 0<p ∧ 0<q ∧ a+b-1=h ∧ p+q-1=uniformEnvelope G h ∧
      Forces G (forest (fun _ : Fin p => a)) (forest (fun _ : Fin q => b)) := by
  classical
  unfold uniformEnvelope at pos ⊢
  obtain ⟨w,_,bound,hw⟩ := Nat.findGreatest_pos.mp pos
  exact Nat.findGreatest_spec bound hw

theorem uniformEnvelope_eq_zero_iff (G : SimpleGraph X) (h : ℕ) :
    uniformEnvelope G h = 0 ↔ ∀ w, ¬ UniformWidthWitness G h w := by
  constructor
  · intro zero w hw
    obtain ⟨a,b,p,q,ha,hb,hp,hq,height,_,force⟩ := hw
    have := uniform_pair_le_envelope G a b p q h ha hb hp hq height force
    omega
  · intro none
    by_contra! positive
    exact none _ (uniformEnvelope_attained G h (by omega))

theorem widthAt_le_uniformEnvelope {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j) (G : SimpleGraph X)
    (r h : ℕ) (row : ForcingRow G s t (padDemand n) (padDemand m) r) (pos : 0<h) :
    widthAt n m r h ≤ uniformEnvelope G h := by
  by_cases live : 0<widthAt n m r h
  · obtain ⟨a,b,p,q,ha,hb,height,hp,hq,width,forces⟩ :=
      column_uniform_forcing hs ht n m hn hm pn pm G r h row pos live
    exact width.trans (uniform_pair_le_envelope G a b p q h ha hb hp hq height forces)
  · omega

theorem uniformEnvelope_le_deletion (G : SimpleGraph X) (j : ℕ) (pos : 0<j) :
    uniformEnvelope G (j+1) ≤ deletionBudget G j := by
  by_cases live : 0<uniformEnvelope G (j+1)
  · obtain ⟨a,b,p,q,ha,hb,hp,hq,height,eq,forces⟩ := uniformEnvelope_attained G _ live
    exact eq ▸ uniform_le_deletion G a b p q j ha hb hp hq pos height forces
  · omega

#print axioms uniform_pair_le_envelope
#print axioms uniformEnvelope_attained
#print axioms uniformEnvelope_eq_zero_iff
#print axioms widthAt_le_uniformEnvelope
#print axioms uniformEnvelope_le_deletion
end JSP452Audit.StarHost
