import TotalLayerDegreesAndUncoveredVerticesPayTheSameCutOnce
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {p q h:ℕ}

theorem nat_original_cut_bill (S T:Set X) (need:(h:ℤ)≤originalFactorCut G p q S T) :
    h+p*S.ncard+q*T.ncard≤(uniformOddPieces G p q S T).ncard+crossCount G T S := by
  rw [uniform_factor_cut_on_original] at need
  exact_mod_cast (show (h:ℤ)+(p:ℤ)*S.ncard+(q:ℤ)*T.ncard≤((uniformOddPieces G p q S T).ncard:ℤ)+(crossCount G T S:ℤ) by omega)

theorem odd_scaled_factor_failure (K:DegreeRegion G (p+q)) (P:ScaledPortPlan K q (p-1)) (E:PortGraphLayers P)
    (odd:Odd (p+q)) (a:Odd p) (pos:0<p) (cap:∀v,Nat.card (G.neighborSet v)≤p+q)
    (S T:Set X) (apart:Disjoint S T) (need:(h:ℤ)≤originalFactorCut G p q S T) :
    (p+q-1)*h≤∑t:Fin q,(E.missing t).ncard := by
  let D := p+q
  let c := p-1
  let Z := (uniformOddPieces G p q S T).ncard+crossCount G T S
  let m := ∑t:Fin q,(E.missing t).ncard
  let A := ∑t:Fin q,originalDegreeSum (E.graph t) S
  have whole := nat_original_cut_bill S T need
  change h+p*S.ncard+q*T.ncard≤Z at whole
  have degree := odd_cut_actual_source_degree p q odd a cap S T apart
  change Z≤originalDegreeSum G S at degree
  have scaled := Nat.mul_le_mul_left c degree
  have sources := E.selected_side_degree_price cap S
  change c*originalDegreeSum G S+A≤(c*D+q)*S.ncard at sources
  have edges := E.all_layers_matching_cut p q rfl a (by omega) cap S T apart
  change q*Z≤A+q*((D-1)*T.ncard)+m at edges
  have exact : D-1=c+q := by dsimp only [D,c];omega
  have pform : p=c+1 := by dsimp only [c];omega
  have fee : c*D+q=(D-1)*p := by
    rw [exact];change c*(p+q)+q=(c+q)*p;rw [pform];ring
  rw [fee] at sources
  have upper : (D-1)*Z≤(D-1)*(p*S.ncard+q*T.ncard)+m := by
    rw [show (D-1)*(p*S.ncard+q*T.ncard)=(D-1)*p*S.ncard+q*((D-1)*T.ncard) by ring]
    rw [show (D-1)*Z=c*Z+q*Z by rw [exact,Nat.add_mul]];omega
  have lower := Nat.mul_le_mul_left (D-1) whole
  rw [show (D-1)*(h+p*S.ncard+q*T.ncard)=(D-1)*h+(D-1)*(p*S.ncard+q*T.ncard) by ring] at lower
  change (D-1)*h≤m;omega

#print axioms nat_original_cut_bill
#print axioms odd_scaled_factor_failure
end JSP452Audit.StarHost
