package de.uka.ilkd.key.axiom_abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * The Zero element of the sign lattice, representing
 * only the number 0.
 * 
 * @author Dominic Scheurer
 */
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
   public Term getDefiningAxiom(Term varOrConst, Services services) {
      TermBuilder tb = services.getTermBuilder();
      return services.getTermBuilder().equals(varOrConst, tb.zero());
   }

   @Override
   public String toParseableString(Services services) {
       return toString();
   }

}
