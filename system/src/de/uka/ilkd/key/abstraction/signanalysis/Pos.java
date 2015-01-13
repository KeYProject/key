package de.uka.ilkd.key.abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ParsableVariable;

public class Pos extends SignAnalysisDomainElem {

   private static final Pos INSTANCE = new Pos();
   
   private Pos() {}
   
   public static Pos getInstance() {
      return INSTANCE;
   }
   
   @Override
   public Name name() {
      return new Name("pos");
   }

   @Override
   public Term getDefiningAxiom(ParsableVariable var, Services services) {
      TermBuilder tb = services.getTermBuilder();
      return services.getTermBuilder().gt(tb.var(var), tb.zero());
   }

}
