// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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

import java.io.IOException;
import java.io.InputStream;
import org.apache.log4j.Logger;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.proof.Goal;

/** This class is responsible for invoking the back-end decision procedure SVC on a
 * <tt>Benchmark</tt>, evaluating its results and returning them represented properly to 
 * <tt>DecisionProcedureSmtAuflia</tt>   
 * 
 * @author akuwertz
 * @version 1.0,  05/29/2006
 */

public class DecisionProcedureSVC extends DecisionProcedureSmtAuflia {

    /** A <tt>String</tt> representation of the command used to execute SVC */
    private static final String SVCCommand = "svc";
    
    /** A <tt>String</tt> representing the answer of SVC if it found a benchmark to be
     * unsatisfiable */
    private static final String SVCUnsatAnwser = "unsat";
    
    /** A <tt>Logger</tt> for monitoring and logging of progress in the decision procedure */
    private static final Logger 
        logger = Logger.getLogger( DecisionProcedureSVC.class.getName() );
    // Logger is created hierarchical to inherit configuration and behaviour from parent
    
    
    /** A mere constructor.
     * 
     * @param goal the <tt>Goal</tt> which should be checked for satisfiability
     * @param dptf the <tt>DecisionProcedureTranslationFactory</tt> used to ranslate the the
     *             sequent of the goal
     * @param services the <tt>Services</tt> used during the translation process 
     */
    public DecisionProcedureSVC( Goal goal, DecisionProcedureTranslationFactory dptf,
                                 Services services) {
        super(goal, dptf, services);
    }

    
    /** This method is reponsible executing and evaluating SVC. It implements the hook provided in 
     * <tt>DecisionProcedureSmtAuflia</tt>
     * 
     *  @throws RuntimeException if an <tt>Exception</tt> occured due to the invocation or 
     *                           execution of SVC
     */
    protected DecisionProcedureResult execDecProc() {
    
        try {
            // Run SVC on stored translation result (benchmark)
            logger.info( "Running SVC on created benchmark..." );
            Process p = Runtime.getRuntime().exec( SVCCommand );
            p.getOutputStream().write( getResultBenchmark().toString().getBytes() );
            p.getOutputStream().close();
            logger.info( "SVC exection finished, processing results..." );
            
            // Retrieve results
            InputStream in = p.getInputStream();
            String svcResult = read(in);
            logger.debug( "Retrieved result succussfully!" );
            in.close();
        
            // Create DecisionProcedureResult from SVC results
            boolean result = svcResult.indexOf( SVCUnsatAnwser ) >= 0;
            return new DecisionProcedureResult( result, svcResult, Constraint.BOTTOM );
            
        } catch( IOException e ) {
            logger.info( "An IOException occured:", e );
            final String errorMessage = 
                "\"SVC\" execution failed:\n\n" + e + "\n\n" +
                "To make use of SVC make sure that \n\n" + 
                "1. the binary is named svc "  +
                "2. the directory where the binary resides is in your $PATH variable\n" +
                "3. the binary has executable file permissions.";
            throw new RuntimeException( errorMessage );
        }
    }    
    
}
