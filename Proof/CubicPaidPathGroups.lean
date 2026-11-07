import CubicPathSlice
namespace JSP452Audit.StarHost
open SimpleGraph
namespace CubicPairFamily
variable {X I : Type*} [Fintype X] [Fintype I] (P:CubicPairFamily X I)

private theorem slice_size {n:ℕ} (v:Fin n ↪ X) : (Set.range v).ncard=n := by
  simpa only [Nat.card_fin] using Set.ncard_range_of_injective v.injective

theorem six_path_pays (G:SimpleGraph X) (U:Set X) (v:Fin 6 ↪ X)
    (inside:∀i,v i∈U) (edges:∀i j,(pathGraph 6).Adj i j → G.Adj (v i) (v j))
    (degree:∀x∈U,fourWhiteDegree G U x≤2) (cap:∀x∈U,fourWhiteDegree G U x+P.degree U x≤3) :
    P.PaidRemoval G U := by
  classical
  let T := Set.range v
  have sub : T⊆U := by rintro _ ⟨i,rfl⟩;exact inside i
  have size : T.ncard=6 := slice_size v
  have maximum := four_sum_mono T _ _ (fun x hx => degree x (sub hx))
  rw [four_sum_const,size,internal_cross_account G U T sub] at maximum
  have internal := path_slice_internal G v edges
  change 6-1≤(G.induce T).edgeSet.ncard at internal
  let C : Finset (Fin 6) := {1,4}
  have all : ∀i:Fin 6,i∈C ∨ ∃j∈C,(pathGraph 6).Adj i j := by simp only [pathGraph_adj];decide
  obtain ⟨S,small,hit⟩ := path_slice_cover G v edges C all
  have count : C.card=2 := by decide
  apply P.removal_of_cross_price G U T S sub ⟨v 0,Set.mem_range_self 0⟩ hit cap
  omega

theorem end_three_path_pays (G:SimpleGraph X) (U:Set X) (v:Fin 3 ↪ X)
    (inside:∀i,v i∈U) (edges:∀i j,(pathGraph 3).Adj i j → G.Adj (v i) (v j))
    (endDeg:fourWhiteDegree G U (v 0)≤1) (degree:∀x∈U,fourWhiteDegree G U x≤2)
    (cap:∀x∈U,fourWhiteDegree G U x+P.degree U x≤3) : P.PaidRemoval G U := by
  classical
  let T := Set.range v
  have sub : T⊆U := by rintro _ ⟨i,rfl⟩;exact inside i
  have size : T.ncard=3 := slice_size v
  have first : v 0∈T := Set.mem_range_self 0
  have point (x:X) (hx:x∈T) : fourWhiteDegree G U x+(if v 0=x then 1 else 0)≤2 := by
    by_cases eq:v 0=x
    · subst x;rw [if_pos rfl];omega
    · rw [if_neg eq,Nat.add_zero];exact degree x (sub hx)
  have maximum := four_sum_mono T _ _ point
  rw [four_sum_add,four_sum_const,four_sum_single_label _ _ first,size,internal_cross_account G U T sub] at maximum
  have internal := path_slice_internal G v edges
  change 3-1≤(G.induce T).edgeSet.ncard at internal
  let C : Finset (Fin 3) := {1}
  have all : ∀i:Fin 3,i∈C ∨ ∃j∈C,(pathGraph 3).Adj i j := by simp only [pathGraph_adj];decide
  obtain ⟨S,small,hit⟩ := path_slice_cover G v edges C all
  have count : C.card=1 := by decide
  apply P.removal_of_cross_price G U T S sub ⟨v 0,first⟩ hit cap
  omega

private theorem short_path_cover (n:ℕ) (number:n=3 ∨ n=5) :
    ∃C:Finset (Fin n),(∀i:Fin n,i∈C ∨ ∃j∈C,(pathGraph n).Adj i j) ∧ 5*C.card≤2*n := by
  rcases number with rfl|rfl
  · exact ⟨{1},by simp only [pathGraph_adj];decide,by decide⟩
  · exact ⟨{1,3},by simp only [pathGraph_adj];decide,by decide⟩

theorem short_closed_path_pays {n:ℕ} (G:SimpleGraph X) (U:Set X) (v:Fin n ↪ X)
    (inside:∀i,v i∈U) (edges:∀i j,(pathGraph n).Adj i j → G.Adj (v i) (v j))
    (number:n=3 ∨ n=5) (closed:crossCount G (Set.range v) (U\Set.range v)=0)
    (cap:∀x∈U,fourWhiteDegree G U x+P.degree U x≤3) : P.PaidRemoval G U := by
  classical
  let T := Set.range v
  have sub : T⊆U := by rintro _ ⟨i,rfl⟩;exact inside i
  have size : T.ncard=n := slice_size v
  obtain ⟨C,all,count⟩ := short_path_cover n number
  obtain ⟨S,small,hit⟩ := path_slice_cover G v edges C all
  have pos : T.Nonempty := (Set.ncard_pos (Set.toFinite _)).1 (by omega)
  apply P.removal_of_cross_price G U T S sub pos hit cap
  change crossCount G T (U\T)=0 at closed
  omega

end CubicPairFamily
#print axioms CubicPairFamily.six_path_pays
#print axioms CubicPairFamily.end_three_path_pays
#print axioms CubicPairFamily.short_closed_path_pays
end JSP452Audit.StarHost
