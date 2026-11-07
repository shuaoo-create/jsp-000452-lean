import GenuineUnpaidPureAxis
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def LocalPureWitness {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (ht : 0<t) (r : ℕ) : Prop :=
  let b := m ⟨0,ht⟩
  let H := G.induce K.core
  let μ := matchingEdges H
  let a := K.roots.ncard
  let W := componentBudget H n
  let J := commonErasedDemand n W a μ
  ∃j,3≤j ∧ j+b≤D+1 ∧ UnpaidHeight G K n m r j ∧ WinsHeight n m r j j 1 ∧
    originalThresholdCount J j=0 ∧ originalThresholdCount (W.entries n) j≤a ∧ originalThresholdCount n j≤μ ∧
    a+2*(μ+r+1)<2*(originalThresholdCount n j+t) ∧
    (j≤b → s+originalThresholdCount m j≤originalThresholdCount n j+t)

theorem bound_unpaid_pure_location {s t r D : ℕ} {X : Type u} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀i,1≤m i)
    (top : diagonal n m (r+2)=D+1) (head : n ⟨0,hs⟩=D) (large : 3≤m ⟨0,ht⟩) (sub : m ⟨0,ht⟩<D)
    (d : ℕ) (width : highestWidth n m r<d) (esc : matchingEdges (G.induce K.core)<s)
    (inner : t+d≤matchingEdges (G.induce K.core)+1) (pure : UnpaidPureFromThree G K n m r) :
    LocalPureWitness G K n m ht r := by
  unfold LocalPureWitness
  intro b H μ a W J
  obtain ⟨j,lo,hi,bad,win⟩ := pure
  have cap := full_head_interior_prefix_cap hs ht n m hn hm head (b:=b) rfl top
    (show D+2-b≤D by change 3≤b at large;omega) (by change b<D at sub;omega)
  have price := win.2.2.2.2.2
  rw [original_threshold_one m pm] at price
  have missing := unpaid_height_missing_threshold G K n m r j hn hm pn esc bad j 1 win
  change a+2*μ+widthAt (W.entries n) m (r+a) j+widthAt J m r j<2*widthAt n m r j at bad
  change t+d≤μ+1 at inner
  have cut : j+b≤D+1 := by
    by_contra! later
    have mon := threshold_anti_height n (by omega : D+2-b≤j)
    omega
  refine ⟨j,lo,cut,bad,win,missing.2.1,missing.2.2.2,missing.2.2.1,by omega,?_⟩
  intro blue
  have y := (original_threshold_prefix m hm j ⟨0,ht⟩).1 blue
  have units := original_threshold_one n pn
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (a:=1) (b:=j) (h:=j) (by omega) (units.symm ▸ hs) y
  rw [units] at rect;omega

#print axioms bound_unpaid_pure_location
end JSP452Audit.StarHost