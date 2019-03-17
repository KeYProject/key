package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

public class MatchProgramInstruction implements MatchInstruction {

    private final ProgramElement pe;

    public MatchProgramInstruction(ProgramElement pe) {
        this.pe = pe;
    }

    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions matchConditions,
            Services services) {
        final MatchConditions result = pe.match(
                new SourceData(termPosition.getCurrentSubterm().javaBlock().program(), -1, services),
                matchConditions);
        return result;
    }
}
