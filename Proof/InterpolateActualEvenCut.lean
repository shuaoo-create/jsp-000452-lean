import SamePieceHalfCut
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem same_cut_even_interpolation {X:Type u} [Finite X] (G:SimpleGraph X) (p a b:ℕ)
    (sum:a+b=2*p) (oddA:Odd a) (small:a≤p) (cap:∀x,Nat.card (G.neighborSet x)≤2*p)
    (S T:Set X) (dis:Disjoint S T) :
    ((p:ℤ)-1)*originalFactorCut G a b S T ≤
      ((p:ℤ)-(a:ℤ))*(minimumExposure G (2*p):ℤ)+((a:ℤ)-1)*((oddRegularComponents G (2*p)).ncard:ℤ) := by
  have lo : 1≤a := by obtain ⟨n,eq⟩ := oddA;omega
  have hp : 0<2*p := by omega
  let A := (S.ncard:ℤ)
  let B := (T.ncard:ℤ)
  let Q := ((uniformOddPieces G a b S T).ncard:ℤ)+(crossCount G T S:ℤ)
  let C := ((oddRegularComponents G (2*p)).ncard:ℤ)
  let rho := (minimumExposure G (2*p):ℤ)
  let Z := Q-(a:ℤ)*A-(b:ℤ)*B
  have original : originalFactorCut G a b S T=Z := uniform_factor_cut_on_original G a b S T
  have endpoint := matching_endpoint_cut G (2*p) hp cap S T dis
  rw [uniform_factor_cut_on_original] at endpoint
  have same := same_odd_capacity_piece_family G a b 1 (2*p-1) (by omega) oddA (by decide) S T
  rw [←same] at endpoint
  change Q-1*A-((2*p-1:ℕ):ℤ)*B≤rho at endpoint
  have epCast : ((2*p-1:ℕ):ℤ)=2*(p:ℤ)-1 := by omega
  rw [epCast] at endpoint
  have midNat := half_cut_for_same_pieces G p a b sum cap S T dis
  have mid : Q≤(p:ℤ)*A+(p:ℤ)*B+C := by
    dsimp [Q,A,B,C];exact_mod_cast midNat
  have first := mul_le_mul_of_nonneg_left endpoint (show 0≤(p:ℤ)-(a:ℤ) by omega)
  have second := mul_le_mul_of_nonneg_left (show Q-(p:ℤ)*A-(p:ℤ)*B≤C by omega) (show 0≤(a:ℤ)-1 by omega)
  have bEq : (b:ℤ)=2*(p:ℤ)-(a:ℤ) := by omega
  have eq : ((p:ℤ)-1)*Z=((p:ℤ)-(a:ℤ))*(Q-1*A-(2*(p:ℤ)-1)*B)+((a:ℤ)-1)*(Q-(p:ℤ)*A-(p:ℤ)*B) := by
    dsimp only [Z];rw [bEq];ring
  rw [original,eq]
  exact add_le_add first second

theorem strict_eight_cut_interpolation (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) :
    3*highestWidth F.n F.m F.r≤minimumExposure F.G 8+2*(oddRegularComponents F.G 8).ncard := by
  obtain ⟨i,j,u,v,_,wide,shape,up,vp,force,_⟩ := strict_eight_true_factor_peak F paid eight
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤8 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq eight
  have cut : ∃S T:Set F.X,Disjoint S T ∧ (highestWidth F.n F.m F.r:ℤ)≤originalFactorCut F.G 3 5 S T := by
    rcases shape with ⟨red,blue⟩|⟨red,blue⟩ <;> rw [red,blue] at force
    · obtain ⟨S,T,dis,fee⟩ := original_uniform_factor_cut F.G 4 6 u v (by decide) (by decide) up vp cap force
      exact ⟨S,T,dis,wide ▸ fee⟩
    · obtain ⟨S,T,dis,fee⟩ := original_uniform_factor_cut F.G 4 6 v u (by decide) (by decide) vp up cap (forces_swap force)
      rw [Nat.add_comm v u,wide] at fee;exact ⟨S,T,dis,fee⟩
  obtain ⟨S,T,dis,fee⟩ := cut
  have interp := same_cut_even_interpolation F.G 4 3 5 (by decide) (by decide) (by decide) cap S T dis
  change 3*originalFactorCut F.G 3 5 S T≤1*(minimumExposure F.G 8:ℤ)+2*((oddRegularComponents F.G 8).ncard:ℤ) at interp
  omega

#print axioms same_cut_even_interpolation
#print axioms strict_eight_cut_interpolation
end JSP452Audit.StarHost
