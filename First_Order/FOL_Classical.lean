import First_Order.FOL_Intuitionistic

namespace FOL.Classical

export FOL.Intuitionistic (Formula is_provable mp deduction ex_falso
  forall_elim exists_intro rule_gen rule_exists_elim substF is_free_for is_free_in)

open FOL.Intuitionistic


axiom double_neg_elim (A : Formula) : is_provable (¬¬A → A)

end FOL.Classical
