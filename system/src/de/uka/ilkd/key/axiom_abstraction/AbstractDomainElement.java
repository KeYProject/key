package de.uka.ilkd.key.axiom_abstraction;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;

/**
 * An element of an abstract domain. Elements are described by
 * defining axioms; the main function of this class is to create
 * such defining axioms for given terms, usually Skolem constants
 * or program variables.
 * 
 * @author Dominic Scheurer
 */
public abstract class AbstractDomainElement implements Named {

   /**
    * <p>Return the defining axiom, instantiated for a given
    * Term (skolem constant or logical / program variable).
    * The term can be seen as a representative of this abstract
    * domain element; the returned formula must formally specify
    * this.</p>
    * 
    * <p>If this element describes, for instance, all numbers
    * divisible by 2, the method could return the formula
    * "varOrConst % 2 == 0".</p>
    * 
    * @param varOrConst The logical / program variable or skolem
    *    constant representing an instance of this abstract domain
    *    element.
    * @param services A services object.
    * @return A JavaDL formula expressing that the given variable
    *    or constant represents an instance of this abstract domain
    *    element.
    */
   public abstract Term getDefiningAxiom(Term varOrConst, Services services);
   
   @Override
   public String toString() {
      return name().toString();
   }
   
}
