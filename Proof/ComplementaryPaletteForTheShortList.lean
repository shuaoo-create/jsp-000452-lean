import ExactPaletteLengthAndParity
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem short_list_exact_palette_endpoint {X : Type*} [Finite X] (G J : SimpleGraph X)
    (sub : J≤G) {s t r d : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (pos : 0<d)
    (balance : matchingEdges J+matchingEdges (G \ J)+d=rowCount s t r)
    (short : s≤matchingEdges J) :
    let q := matchingEdges J-s+d+1
    ForestMatchingEndpoint J n q ∧ q≤matchingEdges J ∧
      s+d+2*(∑i,(n i-1)/2)≤matchingEdges J+1 := by
  intro q
  let Y := G \ J
  have inv : G \ Y=J := by
    ext x y
    change (G.Adj x y ∧ ¬(G.Adj x y ∧ ¬J.Adj x y)) ↔ J.Adj x y
    by_cases h : J.Adj x y
    · exact ⟨fun _ => h,fun _ => ⟨sub h,fun e => e.2 h⟩⟩
    · exact ⟨fun e => (e.2 ⟨e.1,h⟩).elim,fun e => (h e).elim⟩
  have same : matchingEdges Y+matchingEdges (G \ Y)+d=rowCount s t r := by
    rw [inv];simpa only [Nat.add_comm (matchingEdges Y)] using balance
  change matchingEdges J+matchingEdges Y+d=s+t-1-r at balance
  have long : matchingEdges Y<t := by omega
  have eq : t-r-matchingEdges Y=q := by dsimp only [q];omega
  obtain ⟨_,_,_,fe,parity⟩ := long_list_exact_palette_endpoint G Y sdiff_le hs ht n m pn pm row pos same long
  rw [inv,eq] at fe
  rw [eq] at parity
  exact ⟨fe,positive_endpoint_rank J hs n pn fe,by dsimp only [q] at parity;omega⟩

theorem strict_nine_short_adapted_endpoints (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (R : NinePortRegion F.G) :
    let P := R.totalCapacity
    let d := F.rank-matchingEdges F.G
    (F.s≤P → ForestMatchingEndpoint R.adapted F.n (P-F.s+d+1) ∧
      F.s+d+2*(∑i,(F.n i-1)/2)≤P+1) ∧
    (F.t≤P → ForestMatchingEndpoint R.adapted F.m (P-F.t+d+1) ∧
      F.t+d+2*(∑j,(F.m j-1)/2)≤P+1) := by
  intro P d
  have below := (minimal_rank_exact_source F paid).2.2.1
  have pos : 0<d := by dsimp only [d];omega
  obtain ⟨inside,ext,_⟩ := R.exact_port_partition
  have full : matchingEdges R.adapted+matchingEdges R.erased+d=rowCount F.s F.t F.r := by
    change matchingEdges R.adapted+matchingEdges R.erased+d=F.rank
    dsimp only [d];omega
  constructor
  · intro size
    have pack := short_list_exact_palette_endpoint F.G R.adapted R.adapted_le F.hs F.ht F.n F.m
      F.pn F.pm F.row pos full (inside.symm ▸ size)
    simp only [inside] at pack
    exact ⟨pack.1,pack.2.2⟩
  · intro size
    have flip : matchingEdges R.adapted+matchingEdges R.erased+d=rowCount F.t F.s F.r := by
      simpa only [rowCount,Nat.add_comm F.t F.s] using full
    have pack := short_list_exact_palette_endpoint F.G R.adapted R.adapted_le F.ht F.hs F.m F.n
      F.pm F.pn (swap_positive_forcing_row _ _ _ F.row) pos flip (inside.symm ▸ size)
    simp only [inside] at pack
    exact ⟨pack.1,pack.2.2⟩

#print axioms short_list_exact_palette_endpoint
#print axioms strict_nine_short_adapted_endpoints
end JSP452Audit.StarHost
