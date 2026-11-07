import ZeroRootLossClosesRegularRegion
namespace JSP452Audit.StarHost
open SimpleGraph

theorem regular_region_parity {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ) (W:Set X)
    (closed:∀v∈W,∀w,G.Adj v w → w∈W) (full:∀v∈W,Nat.card (G.neighborSet v)=D)
    (covers:∀v,G.connectedComponentMk v∈oddRegularComponents G D → v∈W) :
    ∃k:ℕ,W.ncard=2*k+(oddRegularComponents G D).ncard := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  let part (c:G.ConnectedComponent) := c.supp∩W
  let Z := oddRegularComponents G D
  have union : (⋃c,part c)=W := by
    ext x
    exact ⟨fun h => by obtain ⟨_,hx⟩ := Set.mem_iUnion.mp h;exact hx.2,
      fun hx => Set.mem_iUnion.mpr ⟨G.connectedComponentMk x,rfl,hx⟩⟩
  have dis : Pairwise (Function.onFun Disjoint part) := by
    intro c e ne
    exact Set.disjoint_left.mpr fun x hc he => ne ((show G.connectedComponentMk x=c from hc.1).symm.trans he.1)
  have per (c:G.ConnectedComponent) : (part c).ncard=2*((part c).ncard/2)+(if c∈Z then 1 else 0) := by
    rcases (part c).eq_empty_or_nonempty with empty|non
    · have out : c∉Z := by
        intro inside
        obtain ⟨v,hv⟩ := c.nonempty_supp
        have owned : G.connectedComponentMk v=c := hv
        have w := covers v (owned ▸ inside)
        have no : v∈(∅:Set X) := empty ▸ (show v∈part c from ⟨hv,w⟩)
        exact no
      simp [empty,out]
    · obtain ⟨v,cv,wv⟩ := non
      have contained := cubic_closed_component G W v wv closed
      rw [show G.connectedComponentMk v=c from cv] at contained
      have all : part c=c.supp := Set.inter_eq_left.mpr contained
      have iffOdd : c∈Z ↔ Odd c.supp.ncard := by
        constructor
        · exact fun mem => mem.1
        · exact fun odd => ⟨odd,fun x hx => full x (contained hx)⟩
      rw [all]
      by_cases inside : c∈Z
      · rw [if_pos inside]
        have ⟨q,eq⟩ := iffOdd.mp inside
        omega
      · rw [if_neg inside]
        have even : Even c.supp.ncard := Nat.not_odd_iff_even.mp (fun odd => inside (iffOdd.mpr odd))
        obtain ⟨q,eq⟩ := even
        omega
  have totals := Finset.sum_congr (s₁:=(Finset.univ:Finset G.ConnectedComponent)) rfl (fun c _ => per c)
  rw [Finset.sum_add_distrib,←Finset.mul_sum] at totals
  have count : (∑c:G.ConnectedComponent,if c∈Z then 1 else 0)=Z.ncard := by
    simp [Finset.sum_boole,Set.ncard_eq_toFinset_card']
  rw [count] at totals
  have sum := Set.ncard_iUnion_of_finite (fun c => (part c).toFinite) dis
  rw [union,finsum_eq_sum_of_fintype] at sum
  exact ⟨_,sum.trans totals⟩

#print axioms regular_region_parity
end JSP452Audit.StarHost
