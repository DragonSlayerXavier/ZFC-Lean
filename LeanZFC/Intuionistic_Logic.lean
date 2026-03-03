import LeanZFC.Minimal_Logic

namespace ZFC

-- Ex Falso Quodlibet
axiom ex_falso_quodlibet (A : Prop) : False → A -- From False, anything follows
