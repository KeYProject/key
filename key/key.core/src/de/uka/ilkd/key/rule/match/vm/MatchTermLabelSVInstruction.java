package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.TermLabelSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.VMTacletMatcher.TermNavigator;

public class MatchTermLabelSVInstruction extends Instruction<TermLabelSV> {

    public MatchTermLabelSVInstruction(TermLabelSV op) {
        super(op);
    }

    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions mc,
            Services services) {
        final MatchConditions result = op.match(termPosition.getCurrentSubterm(), mc, services);
        return result;
    }

}
