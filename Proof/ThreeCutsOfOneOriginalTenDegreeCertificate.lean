import OriginalTenDegreeInventory
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem three_prices_of_ten_cut {X:Type u} [Finite X] (G:SimpleGraph X)
    (cap:∀x,Nat.card (G.neighborSet x)≤10) (S T:Set X) (dis:Disjoint S T) :
    let E := originalFactorCut G 1 9 S T
    let Z := originalFactorCut G 3 7 S T
    let C := originalFactorCut G 5 5 S T
    let k := (S.ncard:ℤ)-(T.ncard:ℤ)
    E=Z+2*k ∧ C=Z-2*k ∧ E≤(minimumExposure G 10:ℤ) ∧ C≤((oddRegularComponents G 10).ncard:ℤ) := by
  intro E Z C k
  have endpoint := matching_endpoint_cut G 10 (by decide) cap S T dis
  have mid := balanced_cut_le_original_odd_regular G 5 cap S T dis
  refine ⟨?_,?_,endpoint,mid⟩
  · dsimp only [E,Z,k]
    rw [uniform_factor_cut_on_original,uniform_factor_cut_on_original,
      same_odd_capacity_piece_family G 1 9 3 7 (by decide) (by decide) (by decide)]
    push_cast;ring
  · dsimp only [C,Z,k]
    rw [uniform_factor_cut_on_original,uniform_factor_cut_on_original,
      same_odd_capacity_piece_family G 5 5 3 7 (by decide) (by decide) (by decide)]
    push_cast;ring

theorem strict_ten_balanced_or_outer (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) :
    let h := highestWidth F.n F.m F.r
    h≤(oddRegularComponents F.G 10).ncard ∨
    ∃S T:Set F.X,Disjoint S T ∧ (h:ℤ)≤originalFactorCut F.G 3 7 S T := by
  intro h
  obtain ⟨i,j,u,v,_,wide,shape,up,vp,force,_⟩ := strict_ten_true_factor_peak F paid ten
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤10 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq ten
  rcases shape with ⟨red,blue⟩|⟨red,blue⟩|⟨red,blue⟩ <;> rw [red,blue] at force
  · obtain ⟨S,T,dis,fee⟩ := original_uniform_factor_cut F.G 4 8 u v (by decide) (by decide) up vp cap force
    rw [wide] at fee
    exact Or.inr ⟨S,T,dis,fee⟩
  · obtain ⟨S,T,dis,fee⟩ := original_uniform_factor_cut F.G 4 8 v u (by decide) (by decide) vp up cap (forces_swap force)
    rw [Nat.add_comm v u,wide] at fee
    exact Or.inr ⟨S,T,dis,fee⟩
  · obtain ⟨S,T,dis,fee⟩ := original_uniform_factor_cut F.G 6 6 u v (by decide) (by decide) up vp cap force
    have mid := balanced_cut_le_original_odd_regular F.G 5 cap S T dis
    change originalFactorCut F.G 5 5 S T≤((oddRegularComponents F.G 10).ncard:ℤ) at mid
    change (u+v-1:ℕ)≤originalFactorCut F.G 5 5 S T at fee
    rw [wide] at fee
    exact Or.inl (by omega)

#print axioms three_prices_of_ten_cut
#print axioms strict_ten_balanced_or_outer
end JSP452Audit.StarHost
