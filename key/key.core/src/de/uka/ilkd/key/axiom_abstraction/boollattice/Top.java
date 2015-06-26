package de.uka.ilkd.key.axiom_abstraction.boollattice;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * The Top element of the boolean lattice, representing
 * all booleans (i.e., true and false).
 * 
 * @author Dominic Scheurer
 */
public class Top extends BooleanDomainElem {

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
   public Term getDefiningAxiom(Term varOrConst, Services services) {
      TermBuilder tb = services.getTermBuilder();
      return tb.tt();
   }

}
