package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.rule.MatchConditions;

public class MatchSortDependingFunctionInstr extends Instruction<SortDependingFunction> {

   protected MatchSortDependingFunctionInstr(SortDependingFunction op) {
      super(op);
   }

   @Override
   public MatchConditions match(Operator p_op, MatchConditions mc,
         Services services) {
      return op.match(p_op, mc, services);
   }

}
