package de.uka.ilkd.key.axiom_abstraction.signanalysis;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * The Leq element of the sign lattice, representing
 * all negative numbers and zero.
 * 
 * @author Dominic Scheurer
 */
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
   public Term getDefiningAxiom(Term varOrConst, Services services) {
      TermBuilder tb = services.getTermBuilder();
      return services.getTermBuilder().leq(varOrConst, tb.zero());
   }

   @Override
   public String toParseableString(Services services) {
       return toString();
   }

}
