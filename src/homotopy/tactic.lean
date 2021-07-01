import homotopy.path

/-!
# Tactics

In this file we define some basic tactics which make constructing `path_homotopy`s easier.
-/

namespace path_homotopy.tactic

/-- Associate the left hand side of a homotopy to the left -/
meta def assocl : tactic unit := `[refine homotopy_with.trans path_homotopy.assoc _]
/-- Associate the left hand side of a homotopy to the right -/
meta def assocr : tactic unit := `[refine homotopy_with.trans path_homotopy.assoc.symm _]
/-- Associate the right hand side of a homotopy to the left -/
meta def assocl' : tactic unit := `[refine homotopy_with.trans _ path_homotopy.assoc]
/-- Associate the right hand side of a homotopy to the right -/
meta def assocr' : tactic unit := `[refine homotopy_with.trans _ path_homotopy.assoc.symm]

end path_homotopy.tactic
