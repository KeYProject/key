package de.uka.ilkd.key.abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;

public class Top extends SignAnalysisDomainElem {

   private static final Top INSTANCE = new Top();
   
   private Top() {}
   
   public static Top getInstance() {
      return INSTANCE;
   }
   
   @Override
   public Name name() {
      return new Name("top");
   }

   @Override
   public Term getDefiningAxiom(LogicVariable var, Services services) {
      TermBuilder tb = services.getTermBuilder();
      return tb.inInt(tb.var(var));
   }

}
