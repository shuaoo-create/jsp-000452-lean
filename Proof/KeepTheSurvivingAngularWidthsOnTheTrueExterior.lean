import EachLowerColumnOnTheInducedExteriorPaysAtMostHalfTheOrder
namespace JSP452Audit.StarHost.TenPortSupport
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {K:TenBlockPartition G} {q:ℕ} (W:TenPortSupport G K q)

theorem typed_on_exterior {a b l:ℕ} (pa:0<a) (pb:0<b) (source:ExactTypedWidth (G \ W.piece) a b l) :
    ExactTypedWidth W.outside a b l := by
  rcases source with zero|⟨u,v,pu,pv,eq,rest⟩
  · exact Or.inl zero
  · exact Or.inr ⟨u,v,pu,pv,eq,W.actual_exterior_forces _ _ (fun _ => pa) (fun _ => pb) rest⟩

theorem real_typed_rectangle {s t r a b:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (pa:0<a) (pb:0<b) (survive:W.starTax a<originalThresholdCount n a) (opp:0<originalThresholdCount m b)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) :
    ExactTypedWidth W.outside a b (originalThresholdCount n a+originalThresholdCount m b-1-r-W.starTax a) :=
  W.typed_on_exterior pa pb (W.active_port_rectangle n m hn hm survive opp row)

#print axioms typed_on_exterior
#print axioms real_typed_rectangle
end JSP452Audit.StarHost.TenPortSupport
