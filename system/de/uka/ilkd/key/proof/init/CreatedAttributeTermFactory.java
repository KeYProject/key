// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.AbstractCollectionSort;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;


/**
 * Convenience class for creating terms related to the implicit 
 * "created" attribute.
 * Should possibly be merged into TermBuilder?
 */
public class CreatedAttributeTermFactory {
    public static final CreatedAttributeTermFactory INSTANCE 
            = new CreatedAttributeTermFactory();
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    
    private CreatedAttributeTermFactory() {}
       
    
    /**
     * Creates the formula "objectTerm.<created> = TRUE".
     */
    public Term createCreatedTerm(Services services, Term objectTerm) {
        JavaInfo javaInfo = services.getJavaInfo();
        ProgramVariable createdAttribute
                = javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CREATED, 
                                        javaInfo.getJavaLangObject());
        Term createdTerm = TB.dot(objectTerm, createdAttribute);
        
        return TB.equals(createdTerm, TB.TRUE(services));
    }
    
    
    /**
     * Creates the formula "objectTerm.<created> = TRUE | objectTerm = null"
     */
    public Term createCreatedOrNullTerm(Services services, Term objectTerm) {
        Term objectCreatedTerm = createCreatedTerm(services, objectTerm);
        Term objectNullTerm = TB.equals(objectTerm, TB.NULL(services));
        return TB.or(objectCreatedTerm, objectNullTerm);
    }


    /**
     * Creates the formula "objectTerm.<created> = TRUE & objectTerm != null"
     */
    public Term createCreatedAndNotNullTerm(Services services, Term objectTerm) {
        Term objectCreatedTerm = createCreatedTerm(services, objectTerm);
        Term objectNotNullTerm 
            = TB.not(TB.equals(objectTerm, TB.NULL(services))); 
        return TB.and(objectCreatedTerm, objectNotNullTerm);
    }


    private Term createQuantifierTerm(Services services,
                                      Quantifier q,
                                      LogicVariable[] vars,
                                      Term subTerm,
                                      boolean nullForbidden) {
        //create conjunction of guard terms for all variables of a
        //non-primitive type
        Term guardConjunctionTerm = TB.tt();
        for(int i = 0; i < vars.length; i++) {
            if(!(vars[i].sort() instanceof PrimitiveSort) &&
               !(vars[i].sort() instanceof AbstractCollectionSort)) {
                Term variableTerm = TB.var(vars[i]);
                Term guardTerm
                        = (nullForbidden
                           ? createCreatedAndNotNullTerm(services, variableTerm)
                           : createCreatedOrNullTerm(services, variableTerm));
                guardConjunctionTerm 
                       = TB.and(guardConjunctionTerm, guardTerm);
            }
        }

        //create guarded quantification
        Term quantifierTerm;
        if(q.equals(Quantifier.ALL)) {
            Term guardedTerm = TB.imp(guardConjunctionTerm, subTerm);
            quantifierTerm = TB.all(vars, guardedTerm);
        } else {
            Term guardedTerm = TB.and(guardConjunctionTerm, subTerm);
            quantifierTerm = TB.ex(vars, guardedTerm);
        }
        
        return quantifierTerm;
    }
    
    
    /**
     * Creates a quantifier term where the quantification only covers 
     * objects which have already been created and which are not null.
     */
    public Term createCreatedNotNullQuantifierTerm(Services services,
                                                   Quantifier q, 
                                                   LogicVariable[] vars, 
                                                   Term subTerm) {
        return createQuantifierTerm(services, q, vars, subTerm, true);
    }
    

    /**
     * Creates a quantifier term where the quantification only covers 
     * objects which have already been created and which are not null.
     */
    public Term createCreatedNotNullQuantifierTerm(Services services,
	                                           Quantifier q,
			                           LogicVariable var,
			                           Term subTerm) {
        return createCreatedNotNullQuantifierTerm(services,
	                                          q,
				                  new LogicVariable[] {var},
				                  subTerm);
    }

    
    /**
     * Creates a quantifier term where the quantification only covers 
     * objects which have already been created and which are not null.
     */
    public Term createCreatedOrNullQuantifierTerm(Services services,
                                                   Quantifier q, 
                                                   LogicVariable[] vars, 
                                                   Term subTerm) {
        return createQuantifierTerm(services, q, vars, subTerm, false);
    }
    

    /**
     * Creates a quantifier term where the quantification only covers 
     * objects which have already been created and which are not null.
     */
    public Term createCreatedOrNullQuantifierTerm(Services services,
                                                   Quantifier q,
                                                   LogicVariable var,
                                                   Term subTerm) {
        return createCreatedOrNullQuantifierTerm(services,
                                                  q,
                                                  new LogicVariable[] {var},
                                                  subTerm);
    }
}
