package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.rule.MatchConditions;

public interface IMatchInstruction<PatternType extends SVSubstitute> {

   public MatchConditions match(PatternType p_toMatch, 
         MatchConditions matchConditions, Services services);
   
   
}