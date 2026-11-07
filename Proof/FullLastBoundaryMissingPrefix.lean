import OriginalFullUnitExteriorsExcluded
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Only a positive prefix at the top is needed. Every later red
prefix is then bounded by the offset plus the actual highest width. -/
theorem full_head_interior_prefix_cap {s t r D x b : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (head : n ⟨0,hs⟩=D) (blue : m ⟨0,ht⟩=b) (top : diagonal n m (r+2)=D+1)
    (xcap : x≤D) (level : x+b-1=D+1) :
    originalThresholdCount n x≤r+highestWidth n m r := by
  have px := (original_threshold_prefix n hn x ⟨0,hs⟩).1 (xcap.trans_eq head.symm)
  have py := (original_threshold_prefix m hm b ⟨0,ht⟩).1 blue.ge
  have rect := actual_rectangle_le_column (r:=r) n m hn hm level px py
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm;rw [top] at peak;rw [peak] at rect
  omega

theorem full_last_forces_small_two_prefix {s t r D : ℕ} {X : Type*} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pm : ∀j,1≤m j) (deg : 6≤D) (top : diagonal n m (r+2)=D+1)
    (head : n ⟨0,hs⟩=D) (blue : m ⟨0,ht⟩=D-1) (d : ℕ) (width : highestWidth n m r<d)
    (inner : t+d≤matchingEdges (G.induce K.core)+1) (kinds : SingleUnpaidKinds G K n m ht r)
    (missing : MissingHeightWitness G K n m r) : originalThresholdCount n 2≤matchingEdges (G.induce K.core) := by
  let μ := matchingEdges (G.induce K.core)
  let W := componentBudget (G.induce K.core) n
  let a := K.roots.ncard
  let J := commonErasedDemand n W a μ
  have cap := full_head_interior_prefix_cap hs ht n m hn hm head blue top (by omega : 3≤D) (by omega)
  obtain ⟨j,lo,hi,bad,⟨x,y,win⟩,lost⟩ := missing
  have chosen := (lost x y win).2.2.1
  by_cases ex : x=2
  · exact ex ▸ chosen
  obtain ⟨pure,_⟩|⟨two,_⟩ := kinds j x y bad win
  · have eqj : x=j := by have ks := kinds j x y bad win;rcases ks with ⟨_,v⟩|⟨v,_⟩ <;> omega
    have high : 3≤x := by omega
    have monotone := threshold_anti_height n high
    have price := win.2.2.2.2.2
    rw [pure,original_threshold_one m pm] at price
    change t+d≤μ+1 at inner
    change a+2*μ+widthAt (W.entries n) m (r+a) j+widthAt J m r j<2*widthAt n m r j at bad
    omega
  · exact False.elim (ex two)

#print axioms full_head_interior_prefix_cap
#print axioms full_last_forces_small_two_prefix
end JSP452Audit.StarHost