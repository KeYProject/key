package de.uka.ilkd.key.abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ParsableVariable;

public class Zero extends SignAnalysisDomainElem {

   private static final Zero INSTANCE = new Zero();
   
   private Zero() {}
   
   public static Zero getInstance() {
      return INSTANCE;
   }
   
   @Override
   public Name name() {
      return new Name("zero");
   }

   @Override
   public Term getDefiningAxiom(ParsableVariable var, Services services) {
      TermBuilder tb = services.getTermBuilder();
      return services.getTermBuilder().equals(tb.var(var), tb.zero());
   }

}
