// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.ldt.AbstractIntegerLDT;
import de.uka.ilkd.key.ldt.LDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;


/**
 * Convenience class for creating terms related to the implicit 
 * "created" attribute.
 * Should possibly be merged into TermBuilder?
 */
public class CreatedAttributeTermFactory {
    public static final CreatedAttributeTermFactory INSTANCE 
            = new CreatedAttributeTermFactory();
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    private CreatedAttributeTermFactory() {}
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Term createQuantifierTerm(Services services,
                                      Quantifier q,
                                      LogicVariable[] vars,
                                      Term subTerm,
                                      boolean nullForbidden) {
        //create conjunction of guard terms for all variables of a
        //non-primitive type
        Term guardConjunctionTerm = TB.tt();
        for(int i = 0; i < vars.length; i++) {
            if(!(vars[i].sort().extendsTrans(services.getJavaInfo().objectSort()))) {
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
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------     
    
    /**
     * Creates the formula "objectTerm.<created> = TRUE".
     */
    public Term createCreatedTerm(Services services, Term objectTerm) {
        JavaInfo javaInfo = services.getJavaInfo();
        ProgramVariable createdAttribute
                = javaInfo.getAttribute(ImplicitFieldAdder.IMPLICIT_CREATED, 
                                        javaInfo.getJavaLangObject());
        final Function fieldSymbol = services.getTypeConverter().getHeapLDT().getFieldSymbolForPV(createdAttribute, services);
        Term createdTerm = TB.dot(services, createdAttribute.sort(), objectTerm, fieldSymbol);
        
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
    
    
    /**
     * Creates a formula expressing that the value of the passed program 
     * variable is "java-reachable", i.e.:
     * - for an object type variable: the value is "null" or a created object
     * - for an integer type variable: the value satisfies the corresponding 
     *   in-bounds-predicate
     */
    public Term createReachableVariableValueTerm(Services services, 
                                                 ProgramVariable var) {
        if(var == null) {
            return TB.tt();
        } else if(var.sort().extendsTrans(services.getJavaInfo().objectSort())) {
            return createCreatedOrNullTerm(services, TB.var(var)); 
        } else {
            Type varType = var.getKeYJavaType().getJavaType();
            LDT ldt = services.getTypeConverter().getModelFor(varType);
            if(ldt instanceof AbstractIntegerLDT) {
                Function inBoundsPred 
                    = ((AbstractIntegerLDT) ldt).getInBounds();
                return TB.func(inBoundsPred, TB.var(var));
            }
        }
        return TB.tt();
    }    
    
    
    /**
     * Same as createReachableVariableValueTerm(), only for a *list* of 
     * variables. 
     */
    public Term createReachableVariableValuesTerm(Services services, 
                                                  ListOfProgramVariable vars) {
        Term result = TB.tt();
        for(ProgramVariable var : vars) {
            Term varLegalTerm = createReachableVariableValueTerm(services, var);
            result = TB.and(result, varLegalTerm);
        }
        return result;
    }    
}
