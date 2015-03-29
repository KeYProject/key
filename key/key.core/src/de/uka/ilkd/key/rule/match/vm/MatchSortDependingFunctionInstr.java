package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.VMTacletMatcher.TermNavigator;

public class MatchSortDependingFunctionInstr extends
        Instruction<SortDependingFunction> {

    protected MatchSortDependingFunctionInstr(SortDependingFunction op) {
        super(op);
    }

    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions mc,
            Services services) {
        final MatchConditions result = op.match(termPosition.getCurrentSubterm().op(), mc, services);
        if (result != null) {
            termPosition.gotoNext();
        }
        return result;
    }

}
