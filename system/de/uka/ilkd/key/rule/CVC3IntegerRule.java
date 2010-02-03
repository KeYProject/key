// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.decproc.AbstractDecisionProcedure;
import de.uka.ilkd.key.proof.decproc.DecisionProcedureCVC3;
import de.uka.ilkd.key.proof.decproc.DecisionProcedureTranslationFactory;

/** 
 * CVC3 is as its predecessor CVC3 an SMT prover. This rule allows its invocation 
 * from within KeY using the SMT-LIb interface. 
 * @see AbstractIntegerRule
 */
public class CVC3IntegerRule extends AbstractIntegerRule {

    /** A mere constructor.
     * 
     * @param resultWindow a <tt>boolean</tt> indicating if the results of this <tt>Rule</tt>
     *                     should be presented in a separate window
     * @param dptf the <tt>DecisionProcedureTranslationFactory</tt> to be used
     */
    public CVC3IntegerRule( boolean resultWindow, 
            DecisionProcedureTranslationFactory dptf ) {
        super( new Name( "Decision procedure CVC3" ), resultWindow, dptf );
    }

    
    /** A mere constructor for convenience. Creates an <tt>CVC3IntegerRule</tt> with 
     * <tt>resultWindow</tt> set to <tt>true</tt>
     * 
     * @param dptf the <tt>DecisionProcedureTranslationFactory</tt> to be used
     */
    public CVC3IntegerRule( DecisionProcedureTranslationFactory dptf ) {
        this( true, dptf );
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.AbstractIntegerRule#getDecisionProcedure(de.uka.ilkd.key.proof.Goal, de.uka.ilkd.key.logic.Constraint, de.uka.ilkd.key.java.Services)
     */
    protected AbstractDecisionProcedure getDecisionProcedure( Goal goal, Constraint userConstraint,
                                                              Services services ) {
        return new DecisionProcedureCVC3( goal, dptf, services );
    }

    public AbstractIntegerRule clone(DecisionProcedureTranslationFactory dptf) {
        return new CVC3IntegerRule(showResults, dptf);
    }

}
