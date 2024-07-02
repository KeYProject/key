package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

/**
 * Interface that has to be implemented by instructions for the matching virtual machine 
 */
public interface MatchInstruction {

    public MatchConditions match(TermNavigator termPosition,
            MatchConditions matchConditions, Services services);

}