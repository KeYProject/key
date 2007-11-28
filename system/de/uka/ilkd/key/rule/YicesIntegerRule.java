// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.proof.decproc.DecisionProcedureTranslationFactory;
import de.uka.ilkd.key.proof.decproc.DecisionProcedureYices;

/** This class represents the <tt>Rule</tt> for the simplification of a <tt>Goal</tt> by the 
 * decicion procedure Yices
 * 
 * @author akuwertz
 * @version 1.0,  09/20/2006
 */

public class YicesIntegerRule extends AbstractIntegerRule {

    
    /** A mere constructor.
     * 
     * @param resultWindow a <tt>boolean</tt> indicating if the results of this <tt>Rule</tt>
     *                     should be presented in a separate window
     * @param dptf the <tt>DecisionProcedureTranslationFactory</tt> to be used
     */
    public YicesIntegerRule( boolean resultWindow, 
                               DecisionProcedureTranslationFactory dptf ) {
        super( new Name( "Decision procedure Yices" ), resultWindow, dptf );
    }

    
    /** A mere constructor for convenience. Creates an <tt>YicesIntegerRule</tt> with 
     * <tt>resultWindow</tt> set to <tt>true</tt>
     * 
     * @param dptf the <tt>DecisionProcedureTranslationFactory</tt> to be used
     */
    public YicesIntegerRule( DecisionProcedureTranslationFactory dptf ) {
        this( true, dptf );
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.AbstractIntegerRule#getDecisionProcedure(de.uka.ilkd.key.proof.Goal, de.uka.ilkd.key.logic.Constraint, de.uka.ilkd.key.java.Services)
     */
    protected AbstractDecisionProcedure getDecisionProcedure( Goal goal, Constraint userConstraint,
                                                              Services services ) {
        return new DecisionProcedureYices( goal, dptf, services );
    }

    public AbstractIntegerRule clone(DecisionProcedureTranslationFactory dptf) {
        return new YicesIntegerRule(showResults, dptf);
    }

}
