package de.uka.ilkd.key.axiom_abstraction.boollattice;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * The False element of the boolean lattice, representing
 * exactly the boolean false.
 * 
 * @author Dominic Scheurer
 */
public class False extends BooleanDomainElem {

   private static final False INSTANCE = new False();
   
   private False() {}
   
   public static False getInstance() {
      return INSTANCE;
   }
   
   @Override
   public Name name() {
      return new Name("false");
   }

   @Override
   public Term getDefiningAxiom(Term varOrConst, Services services) {
      TermBuilder tb = services.getTermBuilder();      
      return tb.equals(varOrConst, tb.ff());
   }

   @Override
   public String toParseableString(Services services) {
       return toString();
   }

}
