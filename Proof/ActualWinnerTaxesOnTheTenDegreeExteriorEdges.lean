import AllCrossingStarsShareTheSameInternalEndpointBudget
import TrimUniformStarsAtOriginalPorts
namespace JSP452Audit.StarHost.TenPortSupport
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} {K:TenBlockPartition G} {q:ℕ} (R : TenPortSupport G K q)

noncomputable abbrev starTax (a : ℕ) := min R.rank (R.slotDamage a)

theorem port_slot_decreases : Antitone R.slotDamage := by
  intro a b le
  apply Nat.add_le_add_left
  exact Nat.div_le_div_left (by omega : a+1≤b+1) (by omega : 0<a+1)

theorem port_slot_sizes (positive:1≤q) :
    3*R.slotDamage 2≤2*R.half+R.parity+2*R.portCount ∧
    4*R.slotDamage 3≤2*R.half+R.parity+3*R.portCount ∧
    R.slotDamage 3+1≤R.slotDamage 2 ∧ R.slotDamage 2+1≤R.half := by
  have data := R.size_and_fee positive
  have order : R.support.ncard=2*R.half+R.parity := data.2.2.2.1
  have bound : R.portCount≤2 := data.2.1
  have parity := data.2.2.1
  have ample := R.orderFloor
  dsimp only [slotDamage]
  omega

theorem real_star_tax {I : Type*} [Finite I] (A : SimpleGraph X) (sub : A≤(G \ R.piece)) (a : ℕ)
    (f : (forest (fun _ : I => a)).Copy (A⊔R.piece)) :
    (touchedStars A R.piece (fun _ : I => a) f).ncard≤R.starTax a := by
  apply le_min
  · have rank := touchedStars_le_matchingEdges A R.piece _ f
    exact rank
  · exact R.actual_port_star_damage A sub a f

theorem active_port_rectangle {s t r a b : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (red : R.starTax a<originalThresholdCount n a)
    (blue : 0<originalThresholdCount m b) (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    ExactTypedWidth (G \ R.piece) a b (originalThresholdCount n a+originalThresholdCount m b-1-r-R.starTax a) := by
  let A := originalThresholdCount n a
  let B := originalThresholdCount m b
  let M := R.starTax a
  change ExactTypedWidth (G \ R.piece) a b (A+B-1-r-M)
  change M<A at red
  change 0<B at blue
  by_cases dead : A+B-1-r≤M
  · exact Or.inl (by omega)
  let i := min r (A-M-1)
  let j := r-i
  have ix : i+j=r := by dsimp [i,j];omega
  have liveA : i+M<A := by dsimp [i];omega
  have liveB : j<B := by dsimp [i,j];omega
  have orig := uniform_rectangle_at G n m hn hm ix (show i<A by omega) liveB row
  have next := uniform_after_restoring_red G R.piece (eraseInternal_le G _) a b (A-i) (B-j) M
    (fun S sub f => R.real_star_tax S sub a f) orig
  exact Or.inr ⟨A-i-M,B-j,by omega,by omega,by omega,next⟩

theorem typed_width_envelope {a b h l : ℕ} (pa : 0<a) (pb : 0<b) (height : a+b-1=h)
    (actual : ExactTypedWidth (G \ R.piece) a b l) : l≤uniformEnvelope (G \ R.piece) h := by
  rcases actual with zero|⟨u,v,hu,hv,eq,force⟩
  · omega
  · exact eq ▸ uniform_pair_le_envelope (G \ R.piece) a b u v h pa pb hu hv height force

theorem original_port_winner_alternatives {s t r a b h : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (win : WinsHeight n m r h a b)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    (widthAt n m r h≤uniformEnvelope (G \ R.piece) h+R.starTax a) ∨
    (widthAt n m r h≤uniformEnvelope (G \ R.piece) h+R.starTax b) ∨
    (originalThresholdCount n a≤R.starTax a ∧ originalThresholdCount m b≤R.starTax b) := by
  obtain ⟨pa,pb,height,red,blue,w⟩ := win
  by_cases ar : R.starTax a<originalThresholdCount n a
  · have real := R.active_port_rectangle n m hn hm ar blue row
    have price := R.typed_width_envelope pa pb height real
    omega
  by_cases br : R.starTax b<originalThresholdCount m b
  · have real := R.active_port_rectangle m n hm hn br red (swap_positive_forcing_row _ _ _ row)
    have price := R.typed_width_envelope pb pa (by omega : b+a-1=h) real
    omega
  · exact Or.inr (Or.inr ⟨by omega,by omega⟩)

#print axioms port_slot_decreases
#print axioms port_slot_sizes
#print axioms real_star_tax
#print axioms active_port_rectangle
#print axioms typed_width_envelope
#print axioms original_port_winner_alternatives
end JSP452Audit.StarHost.TenPortSupport
