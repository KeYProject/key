package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.rule.MatchConditions;


public class MatchProgramInstruction implements IMatchInstruction<ProgramElement> {

   private final ProgramElement pe;

   public MatchProgramInstruction(ProgramElement pe) {
      this.pe = pe;
   }
   
   @Override
   public MatchConditions match(ProgramElement p_pe, MatchConditions matchCond, Services services) {
      return pe.match(new SourceData(p_pe, -1, services), matchCond);
   }
}
