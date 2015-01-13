package de.uka.ilkd.key.abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ParsableVariable;

public class Leq extends SignAnalysisDomainElem {

   private static final Leq INSTANCE = new Leq();
   
   private Leq() {}
   
   public static Leq getInstance() {
      return INSTANCE;
   }
   
   @Override
   public Name name() {
      return new Name("leq");
   }

   @Override
   public Term getDefiningAxiom(ParsableVariable var, Services services) {
      TermBuilder tb = services.getTermBuilder();
      return services.getTermBuilder().leq(tb.var(var), tb.zero());
   }

}
