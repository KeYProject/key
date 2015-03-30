package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.VMTacletMatcher;
import de.uka.ilkd.key.rule.match.vm.VMTacletMatcher.TermNavigator;

public interface IMatchInstruction {

    public MatchConditions match(TermNavigator termPosition,
            MatchConditions matchConditions, Services services);
}