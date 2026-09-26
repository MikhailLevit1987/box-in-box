import Boxes

/-! Run with `lake env lean CheckAxioms.lean`. Expected output for each theorem:
`depends on axioms: [propext, Classical.choice, Quot.sound]` (no `sorryAx`). -/

#print axioms Boxes.fits_iff_NC
#print axioms Boxes.fits_of_NC
#print axioms Boxes.NC_of_fits
#print axioms Boxes.fitsStrict_iff_shrink
#print axioms Boxes.fitsStrict_iff_NCs
