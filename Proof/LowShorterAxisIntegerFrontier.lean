import StrictDoubleEmbeddingFromFive
namespace JSP452Audit.StarHost

/-- For degrees three and four, original region prices prohibit both a
shorter head below the cap and two list lengths too close for the axis. -/
theorem low_shorter_axis_integer_frontier (D n s t r N E e a μ M k B ζ β ρ h d u v : ℕ)
    (degree : D=3 ∨ D=4) (cap : n≤D) (first : r<s) (ord : s≤t) (mass : M=a+μ)
    (rank : N=M+k+d) (row : N+r+1=s+t) (exposed : 1≤ρ) (width : h≤ρ) (deficit : ρ+1≤d)
    (tail : t+d≤μ+1) (guard : k+2*a+3*d+r≤M+1) (red : u+d≤M+ρ) (blue : v+d≤M+ρ)
    (rankB : k≤B) (edge : 2*e+ζ=2*D*M+D*ρ+β+2*B) (rootCap : ζ≤D*a)
    (root3 : D=3 → ρ≤2 ∧ 3*ρ+ζ≤2*h+2) (root4 : D=4 → 4*ρ+ζ≤2*h+10)
    (subprice : n<D → E≤N+(D-3)*t+u+v+h) (gen : E+t≤(t-1-r)*D+u+v+h)
    (strict : e<E) : n=D ∧ s+r+h≤t := by
  have step : t-1-r+1+r=t := by omega
  have head : n=D := by
    by_contra ne
    have prof := subprice (lt_of_le_of_ne cap ne)
    rcases degree with eq|eq
    · subst D
      have cost := (root3 rfl).2
      norm_num at prof edge
      linarith only [edge,rankB,cost,rank,prof,red,blue,width,deficit,strict,Nat.zero_le β]
    · subst D
      have cost := root4 rfl
      norm_num at prof edge
      have tiny : ρ=1 ∧ a≤1 := by
        have tight : 2*a+4*ρ<8 := by
          linarith only [edge,rankB,cost,rank,prof,red,blue,width,deficit,tail,mass,strict,Nat.zero_le β]
        omega
      linarith only [edge,rankB,rootCap,rank,prof,red,blue,width,deficit,tail,mass,strict,
        tiny.1,tiny.2,Nat.zero_le β]
  refine ⟨head,?_⟩
  clear head
  by_contra! near
  have len : 2*(t-r)≤N+h := by omega
  have tau : t-r+r=t := by omega
  rcases degree with eq|eq
  · subst D
    obtain ⟨small,cost⟩ := root3 rfl
    norm_num at edge
    linarith only [edge,rankB,cost,small,rank,len,gen,step,tau,red,blue,width,deficit,strict,
      Nat.zero_le r,Nat.zero_le β]
  · subst D
    have cost := root4 rfl
    norm_num at edge
    linarith only [edge,rankB,cost,rank,guard,len,gen,step,tau,red,blue,width,deficit,strict,
      Nat.zero_le r,Nat.zero_le a,Nat.zero_le ρ,Nat.zero_le β]

#print axioms low_shorter_axis_integer_frontier
end JSP452Audit.StarHost
