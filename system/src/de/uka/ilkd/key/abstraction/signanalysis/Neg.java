package de.uka.ilkd.key.abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;

public class Neg extends SignAnalysisDomainElem {

   private static final Neg INSTANCE = new Neg();
   
   private Neg() {}
   
   public static Neg getInstance() {
      return INSTANCE;
   }
   
   @Override
   public Name name() {
      return new Name("neg");
   }

   @Override
   public Term getDefiningAxiom(LogicVariable var, Services services) {
      TermBuilder tb = services.getTermBuilder();
      return services.getTermBuilder().lt(tb.var(var), tb.zero());
   }

}
