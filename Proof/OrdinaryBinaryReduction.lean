import BinaryShape
import BinarySuffixCorner
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
/-- Transport arbitrary sorted binary lists by their actual two-head counts,
then retain the original row's entire price in a single ordinary suffix pair. -/
theorem binary_ordinary_reduction {X : Type*} [Finite X] {s t : ℕ}
    (G : SimpleGraph X) (r : ℕ) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (bn : ∀i,n i≤2) (bm : ∀j,m j≤2) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (i : Fin s) (j : Fin t) (pair : i.val+j.val=r) (ni : n i=2) (mj : m j=2) :
    ∃ P Q a b : ℕ, 0<P ∧ 0<Q ∧ Forces G (forest (binaryProfile P a)) (forest (binaryProfile Q b)) ∧
      rowEnergy n m r = 3*(P+Q-1)+2*max a b + min a b := by
  obtain ⟨p,a,seq,_,_,red,_⟩ := binary_shape n hn pn bn
  obtain ⟨q,b,teq,_,_,blue,_⟩ := binary_shape m hm pm bm
  subst s; subst t
  have rn : n = binaryProfile p a := funext red
  have bm' : m = binaryProfile q b := funext blue
  subst n; subst m
  have ip : i.val<p := by by_contra! h; simp [binaryProfile,not_lt.mpr h] at ni
  have jq : j.val<q := by by_contra! h; simp [binaryProfile,not_lt.mpr h] at mj
  obtain ⟨force,energy⟩ := binary_corner_reduction G p a q b r i.val j.val ip jq pair row
  exact ⟨p-i.val,q-j.val,a,b,by omega,by omega,force,energy⟩

theorem degree_two_strict_ordinary (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (small : diagonal F.n F.m (F.r+2)-1≤2) :
    (∀ x, Nat.card (F.G.neighborSet x) ≤ 2) ∧
      ∃ p q a b : ℕ, 0<p ∧ 0<q ∧ Forces F.G (forest (binaryProfile p a)) (forest (binaryProfile q b)) ∧
        F.G.edgeSet.ncard < 3*(p+q-1)+2*max a b+min a b := by
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  obtain ⟨_,binN,binM,i,j,pair,ni,mj⟩ := degree_two_binary_source F paid small
  obtain ⟨p,q,a,b,hp,hq,force,energy⟩ := binary_ordinary_reduction F.G F.r F.n F.m F.hn F.hm F.pn F.pm
    (fun x => by have := binN x; omega) (fun x => by have := binM x; omega) F.row i j pair ni mj
  exact ⟨fun x => (cap x).trans small,p,q,a,b,hp,hq,force,energy ▸ F.strict⟩
#print axioms binary_ordinary_reduction
#print axioms degree_two_strict_ordinary
end JSP452Audit.StarHost