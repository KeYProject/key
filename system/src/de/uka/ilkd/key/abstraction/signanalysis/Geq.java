package de.uka.ilkd.key.abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

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
   public Term getDefiningAxiom(Term varOrConst, Services services) {
      TermBuilder tb = services.getTermBuilder();
      return services.getTermBuilder().geq(varOrConst, tb.zero());
   }

}
