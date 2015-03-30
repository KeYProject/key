package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.VMTacletMatcher;
import de.uka.ilkd.key.rule.match.vm.VMTacletMatcher.TermNavigator;

public class MatchProgramSVInstruction extends Instruction<ProgramSV> {

    public MatchProgramSVInstruction(ProgramSV sv) {
        super(sv);
    }

    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions mc,
            Services services) {
        MatchConditions result = op.match(termPosition.getCurrentSubterm(), mc, services);
        if (result != null) {
            termPosition.gotoNextSibling();
        }
        return result;
    }

}
