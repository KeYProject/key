// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;

/** This class is just a dummy to enable translating a <tt>Sequent</tt> into a <tt>Benchmark</tt> 
 *  and archiving it without calling an external decision procedure 
 *  
 * @author akuwertz
 * @version 1.0,  07/26/2006
 */

public class DecisionProcedureDummyTranslation extends DecisionProcedureSmtAuflia {

   /** A mere constructor.
     * 
     * @param goal the <tt>Goal</tt> which should be checked for satisfiability
     * @param dptf the <tt>DecisionProcedureTranslationFactory</tt> used to ranslate the the
     *             sequent of the goal
     * @param services the <tt>Services</tt> used during the translation process 
     */
    public DecisionProcedureDummyTranslation( Goal goal, DecisionProcedureTranslationFactory dptf,
                                     Services services) {
        super(goal, dptf, services);
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.decproc.DecisionProcedureSmtAuflia#execDecProc()
     */
    protected DecisionProcedureResult execDecProc() {
        // Do nothing, just a dummy!
        return null;
    }
    
}
