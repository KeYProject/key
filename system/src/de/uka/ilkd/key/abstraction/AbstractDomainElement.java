package de.uka.ilkd.key.abstraction;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LogicVariable;

/**
 * TODO: Document.
 * 
 * @author Dominic Scheurer
 */
public interface AbstractDomainElement extends Named {

   /**
    * <p>Return the defining axiom, instantiated for a given
    * logical variable. The variable can be seen as a
    * representative of this abstract domain element; the
    * returned formula must formally specify this.</p>
    * 
    * <p>If this element describes, for instance, all numbers
    * divisible by 2, the method could return the formula
    * "var % 2 == 0".</p>
    * 
    * @param var The logical variable representing an instance
    *    of this abstract domain element.
    * @param services A services object.
    * @return A JavaDL formula expressing that the given variable
    *    represents an instance of this abstract domain element.
    */
   public Term getDefiningAxiom(LogicVariable var, Services services);
   
}
