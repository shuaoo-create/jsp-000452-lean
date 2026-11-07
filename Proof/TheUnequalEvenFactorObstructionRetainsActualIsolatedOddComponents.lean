import TheOriginalOddFactorObstructionRequiresTheRealScaledDeficit
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {p q h:ℕ}

theorem even_scaled_factor_failure (K:DegreeRegion G (p+q)) (P:ScaledPortPlan K (q-p) (p-1)) (E:PortGraphLayers P)
    (even:Even (p+q)) (a:Odd p) (pos:0<p) (less:p≤q) (cap:∀v,Nat.card (G.neighborSet v)≤p+q)
    (S T:Set X) (apart:Disjoint S T) (need:(h:ℤ)≤originalFactorCut G p q S T) :
    (p+q-2)*h≤(∑t:Fin (q-p),(E.missing t).ncard)+2*(p-1)*(oddRegularComponents G (p+q)).ncard := by
  let D := p+q
  let c := p-1
  let k := q-p
  let Z := (uniformOddPieces G p q S T).ncard+crossCount G T S
  let m := ∑t:Fin k,(E.missing t).ncard
  let b := (oddRegularComponents G D).ncard
  let A := ∑t:Fin k,originalDegreeSum (E.graph t) S
  have whole := nat_original_cut_bill S T need
  change h+p*S.ncard+q*T.ncard≤Z at whole
  have degree := even_cut_actual_degree_sum p q even cap S T apart
  change 2*Z≤originalDegreeSum G S+originalDegreeSum G T+2*b at degree
  have scaled := Nat.mul_le_mul_left c degree
  have sources := E.selected_side_degree_price cap S
  change c*originalDegreeSum G S+A≤(c*D+k)*S.ncard at sources
  have edges := E.all_layers_matching_cut p q rfl a (by omega) cap S T apart
  change k*Z≤A+k*((D-1)*T.ncard)+m at edges
  have cb := Nat.mul_le_mul_left c (degree_sum_le_cap G T D (fun x _ => cap x))
  have PF : p=c+1 := by dsimp only [c];omega
  have QF : q=p+k := by dsimp only [k];omega
  have two : D-2=2*c+k := by dsimp only [D,c,k];omega
  have one : D-1=2*c+k+1 := by dsimp only [D,c,k];omega
  have sideS : c*D+k=(D-2)*p := by rw [two];change c*(p+q)+k=(2*c+k)*p;rw [QF,PF];ring
  have sideT : c*D+k*(D-1)=(D-2)*q := by rw [two,one];change c*(p+q)+k*(2*c+k+1)=(2*c+k)*q;rw [QF,PF];ring
  rw [sideS] at sources
  have rhs : (D-2)*(p*S.ncard+q*T.ncard)=((D-2)*p)*S.ncard+c*(D*T.ncard)+k*((D-1)*T.ncard) := by
    calc
      _ = ((D-2)*p)*S.ncard+((D-2)*q)*T.ncard := by ring
      _ = _ := by rw [←sideT];ring
  have upper : (D-2)*Z≤(D-2)*(p*S.ncard+q*T.ncard)+m+2*c*b := by
    rw [rhs,show (D-2)*Z=c*(2*Z)+k*Z by rw [two];ring]
    rw [show c*(originalDegreeSum G S+originalDegreeSum G T+2*b)=c*originalDegreeSum G S+c*originalDegreeSum G T+2*c*b by ring] at scaled
    omega
  have lower := Nat.mul_le_mul_left (D-2) whole
  rw [show (D-2)*(h+p*S.ncard+q*T.ncard)=(D-2)*h+(D-2)*(p*S.ncard+q*T.ncard) by ring] at lower
  change (D-2)*h≤m+2*c*b;omega

#print axioms even_scaled_factor_failure
end JSP452Audit.StarHost
