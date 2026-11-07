import LowStrictOriginalAxis
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- All original root costs plus the edges from roots into the core
partition the full capacity of exactly those roots. -/
theorem root_cost_complement (G : SimpleGraph X) (D : ℕ) (K : DegreeRegion G D)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) :
    rootShortfall G K.roots D+2*(G.induce K.roots).edgeSet.ncard+crossCount G K.roots K.rest+
      crossCount G K.roots K.core=D*K.roots.ncard := by
  obtain ⟨ac,ab,cb,all⟩ := region_partition G K.barrier K.pieces
  have sum := partition_handshake G K.roots K.core K.rest ac ab cb all
  have full : rootShortfall G K.roots D+originalDegreeSum G K.roots=D*K.roots.ncard :=
    Nat.sub_add_cancel (degree_sum_le_cap G K.roots D (fun v _ => cap v))
  omega

/-- Scalar payment at degree four assuming the displayed domination price.
Each variable keeps the sign of the original exterior edge cost. -/
theorem four_axis_domination_payment (s t r M a μ k z e E ρ h d L β V f : ℚ)
    (mass : M=a+μ) (rank : M+k+d=s+t-r-1) (deficit : ρ+1≤d) (exposed : 1≤ρ) (width : h≤ρ)
    (budget : 4*ρ+L≤2*h+10) (root : L≤4*a) (entry : V≤2*s+f) (tail : t+d≤μ+1)
    (unused : 4*V≤3*M+a-3*s+4*ρ-5*d+3) (maxHead : f≤r+h)
    (dom : 87*(t-r)≤66*M+33*ρ+29*z+33*β)
    (axis : E≤4*t-4*r+s+V+h-4) (k0 : 0≤k) (z0 : 0≤z) (r0 : 0≤r)
    (edge : 8*M+4*ρ+2*k+2*z+2*β≤2*e+L) : 10≤66*(e-E) := by
  linarith only [mass,rank,deficit,exposed,width,budget,root,entry,tail,unused,maxHead,dom,axis,k0,z0,r0,edge]

#print axioms root_cost_complement
#print axioms four_axis_domination_payment
end JSP452Audit.StarHost
