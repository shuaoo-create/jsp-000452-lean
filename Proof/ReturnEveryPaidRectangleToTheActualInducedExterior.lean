import ActualWinnerTaxesOnTheTenDegreeExteriorEdges
namespace JSP452Audit.StarHost.TenPortSupport
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {K:TenBlockPartition G} {q:ℕ} (W:TenPortSupport G K q)

theorem actual_exterior_forces {I J:Type*} (n:I→ℕ) (m:J→ℕ) (pn:∀i,0<n i) (pm:∀i,0<m i)
    (source:Forces (G \ W.piece) (forest n) (forest m)) : Forces W.outside (forest n) (forest m) := by
  let O := G \ W.piece
  have lands (x:O.support) : x.val∉W.support := by
    obtain ⟨y,e⟩ := x.property
    intro hit
    exact e.2 ⟨e.1,fun ext => ext.1 hit⟩
  let inc : (O.induce O.support).Copy W.outside := {
    toHom := {toFun := fun x => ⟨x.val,lands x⟩, map_rel' := fun e => e.1}
    injective' := fun _ _ eq => Subtype.ext (congrArg (fun w:↥(W.supportᶜ:Set X) => w.val) eq)}
  exact forced_host_of_copy inc _ _ (forces_on_support O n m pn pm source)

theorem exterior_inventory (j:ℕ) : uniformEnvelope (G \ W.piece) j=uniformEnvelope W.outside j := by
  apply Nat.le_antisymm
  · by_cases live:0<uniformEnvelope (G \ W.piece) j
    · obtain ⟨a,b,p,q,pa,pb,pp,pq,height,wide,forced⟩ := uniformEnvelope_attained _ j live
      exact wide ▸ uniform_pair_le_envelope _ _ _ _ _ _ pa pb pp pq height
        (W.actual_exterior_forces _ _ (fun _ => pa) (fun _ => pb) forced)
    · omega
  · let inc : W.outside.Copy (G \ W.piece) := {
      toHom := {toFun := Subtype.val,map_rel' := fun {x y} e => ⟨e,fun hit => hit.2 ⟨x.property,y.property⟩⟩}
      injective' := Subtype.val_injective}
    exact uniform_envelope_host_copy inc j

theorem actual_exterior_rectangles {s t r a b j:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (win:WinsHeight n m r j a b) (row:ForcingRow G s t (padDemand n) (padDemand m) r) :
    widthAt n m r j≤uniformEnvelope W.outside j+W.starTax a ∨
    widthAt n m r j≤uniformEnvelope W.outside j+W.starTax b ∨
    (originalThresholdCount n a≤W.starTax a ∧ originalThresholdCount m b≤W.starTax b) := by
  rw [←W.exterior_inventory];exact W.original_port_winner_alternatives n m hn hm win row

#print axioms actual_exterior_forces
#print axioms exterior_inventory
#print axioms actual_exterior_rectangles
end JSP452Audit.StarHost.TenPortSupport
