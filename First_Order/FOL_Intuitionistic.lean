import First_Order.FOL_Minimal

namespace FOL.Intuitionistic

export FOL.Minimal (Term Formula is_provable mp deduction aff_cons dist_imp
  conj_intro conj_elim_left conj_elim_right disj_intro_left disj_intro_right disj_elim
  forall_elim exists_intro rule_gen rule_exists_elim substF is_free_for is_free_in)

open FOL.Minimal

axiom ex_falso (A : Formula) : is_provable (Formula.bot → A)

end FOL.Intuitionistic
