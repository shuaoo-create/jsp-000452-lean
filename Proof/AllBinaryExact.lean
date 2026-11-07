import BinaryDegreeTwoLower
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- The foundational low-degree branch is empty for global minimum-rank strict
sources, including when the original lists were not assumed to be binary. -/
theorem strict_source_degree_at_least_three (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) :
    3 ≤ diagonal F.n F.m (F.r+2)-1 := by
  by_contra! small
  obtain ⟨cap,p,q,a,b,hp,hq,force,cheap⟩ := degree_two_strict_ordinary F paid (by omega)
  exact cheap.not_ge (ordinary_binary_degree_two_lower F.G p q a b hp hq cap force)

/-- Every binary profile pair satisfies the original size Ramsey conjecture on
arbitrary finite forcing hosts, not just on graphs of degree at most two. -/
theorem all_binary_sizeRamsey {s t : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (bn : ∀i,n i≤2) (bm : ∀j,m j≤2) :
    sizeRamsey (forest n) (forest m) = ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k := by
  by_contra fail
  obtain ⟨N,G,U,row,rank,_,_,one,_,cap,_,heads⟩ := normalized_source_of_failure hs ht n m hn hm pn pm fail
  let Y := G.induce {x | x∉U}
  obtain ⟨i,j,sum,att⟩ := diagonal_attained n m hs ht U.card (by dsimp [rowCount] at rank; omega)
  have ⟨red,blue⟩ := heads i j sum att
  have hi := bn i
  have hj := bm j
  have maxTwo : ∀ x, Nat.card (Y.neighborSet x) ≤ 2 := fun x => (cap x).trans (by omega)
  obtain ⟨p,q,a,b,hp,hq,force,eq⟩ := binary_ordinary_reduction Y U.card n m hn hm pn pm bn bm row
    i j sum (by omega) (by omega)
  have lower := ordinary_binary_degree_two_lower Y p q a b hp hq maxTwo force
  change Y.edgeSet.ncard+1 = _ at one
  omega

theorem two_and_two_both_fifteen :
    sizeRamsey (forest (binaryProfile 2 2)) (forest (binaryProfile 2 2)) = 15 := by
  rw [all_binary_sizeRamsey (by decide) (by decide) _ _ (binaryProfile_antitone 2 2)
    (binaryProfile_antitone 2 2) (binaryProfile_positive 2 2) (binaryProfile_positive 2 2)
    (by decide) (by decide)]
  decide
#print axioms strict_source_degree_at_least_three
#print axioms all_binary_sizeRamsey
#print axioms two_and_two_both_fifteen
end JSP452Audit.StarHost