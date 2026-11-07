import HighBoundaryEnvelopeFee
namespace JSP452Audit.StarHost

/-- The two lowest interior layers may share their paid width with the
top layer. Keep the two sides of the same blue class difference together.
The allowance 2*rho is charged once for this triple of layers. -/
theorem low_pair_and_top_price (t r a μ u δ d ρ h X Y q g₂ g₃ w₂ w₃ wD c₂ c₃ cD A₂ A₃ : ℕ)
    (rho : h≤ρ) (deficit : ρ+1≤d) (red : a+r+2*(d+X)≤t)
    (embed : t+d+2*Y≤μ+1) (qdef : q=μ-(t+2*Y)+1)
    (blueCount : g₂≤t) (sorted : g₃≤g₂) (mass : t+g₂+d≤μ+a+ρ)
    (outside : a+r+2*(d+Y)+δ≤u) (volume : μ+r+2*d+2*Y≤2*u+2*δ+ρ)
    (base : 2*wD+2*X+2*d≤cD) (fee : a+2*μ≤cD)
    (top : 2*wD+2*X+2*d+2*q≤cD ∨ 2*wD+2*g₃≤2*h+2*g₂)
    (two : 2*w₂≤c₂+A₂ ∨ (2*w₂+2*(u+δ+g₂)≤c₂+2*t ∧ 2*w₂≤c₂+2*q))
    (three : 2*w₃≤c₃+A₃ ∨ 2*w₃+2*(u+δ+g₃)≤c₃+2*g₂) :
    2*w₂+2*w₃+2*wD+2*X+2*d≤c₂+c₃+cD+A₂+A₃+2*ρ := by
  rcases two with plain₂|mix₂ <;> rcases three with plain₃|mix₃ <;> rcases top with hh|b₂ <;> omega

/-- The one-axis inventory also limits the height-two loss by twice
q0, independently of how many genuine two-leaf red stars remain. -/
theorem matching_axis_qbound (f t r a μ Y w v b z : ℕ)
    (space : t+2*Y≤μ) (tpos : 0<t) (choose : w=μ+1-(t+Y)) (live : 0<v)
    (extra : 2*w<f → f-2*w+v-1-(r+a)≤b ∧ f-2*w+v-1-r≤z) :
    2*(f+t-1-r)≤a+2*μ+b+z+2*(μ-(t+2*Y)+1) := by
  by_cases many : 2*w<f
  · obtain ⟨bfee,zfee⟩ := extra many
    omega
  · omega

theorem actual_matching_qbound {s t r D : ℕ} {X : Type*} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (space : t+2*(∑j,(m j-1)/2)≤matchingEdges (G.induce K.core)) (h : ℕ) (pos : 0<h)
    (winner : WinsHeight n m r h h 1) :
    2*widthAt n m r h≤jointLayerCapacity G K h+2*(matchingEdges (G.induce K.core)-(t+2*∑j,(m j-1)/2)+1) := by
  let μ := matchingEdges (G.induce K.core)
  let Y := ∑j,(m j-1)/2
  let w := μ+1-(t+Y)
  let V := halfOrderBudget m (μ-w)
  obtain ⟨live,all⟩ := exact_axis_repair_inventory G K n m hn hm pn pm ht row
    (by change t+Y≤μ;change t+2*Y≤μ at space;omega)
  have eq := winner.2.2.2.2.2
  rw [original_threshold_one m pm] at eq
  rw [eq];unfold jointLayerCapacity
  exact matching_axis_qbound _ t r K.roots.ncard μ Y w V.len _ _ space ht rfl live (all h pos)

#print axioms low_pair_and_top_price
#print axioms matching_axis_qbound
#print axioms actual_matching_qbound
end JSP452Audit.StarHost
