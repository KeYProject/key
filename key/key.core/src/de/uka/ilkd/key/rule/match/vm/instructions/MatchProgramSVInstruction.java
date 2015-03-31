package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

public class MatchProgramSVInstruction extends MatchSchemaVariableInstruction<ProgramSV> {

    public MatchProgramSVInstruction(ProgramSV sv) {
        super(sv);
    }

    private MatchConditions match(Term substitute,  MatchConditions mc, Services services) {

        final ProgramSVSort svSort = (ProgramSVSort)op.sort();

        if (svSort.canStandFor(substitute)) {
            return addInstantiation(substitute, mc, services);
        }
        return null;
    }

    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions mc,
            Services services) {
        MatchConditions result = match(termPosition.getCurrentSubterm(), mc, services);
        if (result != null) {
            termPosition.gotoNextSibling();
        }
        return result;
    }

}
