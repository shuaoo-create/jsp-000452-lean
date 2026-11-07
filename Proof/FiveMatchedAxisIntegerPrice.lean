import FiveOriginalMatchedDomination
import FiveStrictEmbeddedHead
import WeightedEmbeddedMass
import ActualWinningRectangles
namespace JSP452Audit.StarHost

/-- In the long-axis case, the number of original five-leaf stars is
controlled by the top column and a genuine blue two-leaf threshold. -/
theorem five_original_red_mass_upper {s t r : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (cap : ∀i,n i≤5) (head : n ⟨0,hs⟩=5) (live : 0<rowCount s t r)
    (top : diagonal n m (r+2)=6) :
    (∑i,n i)≤4*s+r+highestWidth n m r := by
  let f := originalThresholdCount n 5
  let B := originalThresholdCount m 2
  have fpos : 0<f := (original_threshold_prefix n hn 5 ⟨0,hs⟩).1 head.ge
  obtain ⟨i,j,idx,atTop⟩ := diagonal_attained n m hs ht r (by dsimp [rowCount] at live;omega)
  have capI := cap i
  have b2 : 2≤m j := by omega
  have bj := (original_threshold_prefix m hm 2 j).1 b2
  have bpos : 0<B := by change j.val<B at bj;omega
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (by decide : 5+2-1=6) fpos bpos
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm
  rw [top] at peak
  rw [peak] at rect
  change f+B-1-r≤highestWidth n m r at rect
  have point (i:Fin s) : n i≤4+(if 5≤n i then 1 else 0) := by
    have hi:=cap i;split_ifs <;> omega
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => point i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Finset.sum_boole,Nat.cast_id] at total
  change (∑i,n i)≤s*4+f at total
  omega

/-- The near and far length certificates use only integer units. The
long-axis certificate retains the 8/50 discount per core matching edge. -/
theorem five_matched_axis_integer_price (s t r N E e M a μ k z ζ β ρ h d u v : ℕ)
    (first : r<s) (ordered : s≤t) (mass : M=a+μ) (rank : N=M+k+d) (row : N+r+1=s+t)
    (exposed : 1≤ρ) (deficit : ρ+1≤d) (width : h≤ρ)
    (leafR : u+d≤M+ρ) (leafB : v+d≤M+ρ) (edges : 2*e+ζ=10*M+5*ρ+β+2*(k+z))
    (budget : 3*ρ+ζ+β≤10) (guardR : k+a+2*d+r≤s)
    (guardBoth : k+2*a+3*d+r≤M+1) (inside : s≤μ)
    (general : E+t≤(t-1-r)*5+u+v+h)
    (long : s+r+h≤t → E≤(t-1-r)*5+u+h)
    (unused : 5*u+6*d+1≤4*μ+s+5*(a+ρ)+5)
    (entry : u≤4*s+r+h)
    (pricing : 200*(t-r)+8*μ≤84*(2*M+ρ)+50*z+50*β) : E≤e := by
  have tau : t-r+r=t := by omega
  have step : t-1-r+1+r=t := by omega
  by_cases far : s+r+h≤t
  · have axis := long far
    have muBound : M≤2*μ := by linarith only [guardR,mass,inside,Nat.zero_le k,Nat.zero_le d,Nat.zero_le r]
    have leaves : 6*u+k+8*d≤4*M+6*s+5*ρ+4+h := by
      linarith only [unused,entry,guardR,mass]
    have ledger : 150*E+24*μ+25*k+50*d+500≤150*e+4*M+2*ρ+175*h+75*(ζ+β) := by
      linarith only [edges,axis,tau,step,row,rank,leaves,pricing]
    have combined : 150*E+16*μ+98*ρ≤150*e+200 := by
      linarith only [ledger,muBound,deficit,width,budget,Nat.zero_le k]
    by_contra! bad
    have gap : e+1≤E := by omega
    linarith only [gap,combined,exposed,Nat.zero_le μ]
  · have len : 2*(t-r)≤N+h := by omega
    linarith only [general,tau,step,len,leafR,leafB,edges,rank,guardBoth,width,budget,deficit,
      exposed,Nat.zero_le a,Nat.zero_le r,Nat.zero_le z,Nat.zero_le β]

#print axioms five_original_red_mass_upper
#print axioms five_matched_axis_integer_price
end JSP452Audit.StarHost
