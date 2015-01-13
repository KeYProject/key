package de.uka.ilkd.key.abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ParsableVariable;

public class Geq extends SignAnalysisDomainElem {

   private static final Geq INSTANCE = new Geq();
   
   private Geq() {}
   
   public static Geq getInstance() {
      return INSTANCE;
   }
   
   @Override
   public Name name() {
      return new Name("geq");
   }

   @Override
   public Term getDefiningAxiom(ParsableVariable var, Services services) {
      TermBuilder tb = services.getTermBuilder();
      return services.getTermBuilder().geq(tb.var(var), tb.zero());
   }

}
