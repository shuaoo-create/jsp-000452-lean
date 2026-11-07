import MaximalRetained
namespace JSP452Audit.Padded
open SimpleGraph
/-- Components of the actually retained graph neighboring x in the original graph. -/
def retainedNeighborComponents {X : Type*} (H : SimpleGraph X) (W : Finset X) (x : X) :
    Set (H.induce (W : Set X)).ConnectedComponent :=
  {c | ∃ w : ↥(W : Set X), H.Adj x w.val ∧ (H.induce (W : Set X)).connectedComponentMk w = c}
end JSP452Audit.Padded
