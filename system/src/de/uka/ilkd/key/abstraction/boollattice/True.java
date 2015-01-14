package de.uka.ilkd.key.abstraction.boollattice;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

public class True extends BooleanDomainElem {

   private static final True INSTANCE = new True();
   
   private True() {}
   
   public static True getInstance() {
      return INSTANCE;
   }
   
   @Override
   public Name name() {
      return new Name("true");
   }

   @Override
   public Term getDefiningAxiom(Term varOrConst, Services services) {
      TermBuilder tb = services.getTermBuilder();      
      return tb.equals(varOrConst, tb.tt());
   }

}
