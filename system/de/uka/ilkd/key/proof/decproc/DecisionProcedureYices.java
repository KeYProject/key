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


/** /** This class is responsible for invoking the back-end decision procedure Yices on a
 * <tt>Benchmark</tt>, evaluating its results and returning them represented properly to 
 * <tt>DecisionProcedureSmtAuflia</tt>
 * 
 * @author akuwertz
 * @version 1.0,  09/20/2006
 */

public class DecisionProcedureYices extends DecisionProcedureSmtAuflia {

    /** A <tt>String</tt> representation of the command used to execute Yices */
    private static final String YicesCommand = "yices";
    
     /** <tt>String</tt>s representing the Yicese command option for SMT-LIB support */ 
    private static final String YicesSmtFlag = "-smt";
    
    /** A <tt>String</tt> representing the answer of Yices if it found a benchmark to be
     * unsatisfiable */
    private static final String YicesUnsatAnwser = "unsat";
    
    /** A <tt>Logger</tt> for monitoring and logging of progress in the decision procedure */
    private static final Logger 
        logger = Logger.getLogger( DecisionProcedureYices.class.getName() );
    // Logger is created hierarchical to inherit configuration and behaviour from parent
    
    
    /** A mere constructor.
     * 
     * @param goal the <tt>Goal</tt> which should be checked for satisfiability
     * @param dptf the <tt>DecisionProcedureTranslationFactory</tt> used to ranslate the the
     *             sequent of the goal
     * @param services the <tt>Services</tt> used during the translation process 
     */
    public DecisionProcedureYices( Goal goal, DecisionProcedureTranslationFactory dptf,
                                 Services services) {
        super(goal, dptf, services);
    }

    
    /** This method is reponsible executing and evaluating Yices. It implements the hook provided in 
     * <tt>DecisionProcedureSmtAuflia</tt>
     * 
     *  @throws RuntimeException if an <tt>Exception</tt> occured due to the invocation or 
     *                           execution of Yices
     */
    protected DecisionProcedureResult execDecProc() {
    
        try {
            // Run Yices on stored translation result (benchmark)
            logger.info( "Running Yices on created benchmark..." );
            
            String[] cmdArray = { YicesCommand , YicesSmtFlag, super.getTempFile().getPath() };
            Process p = Runtime.getRuntime().exec( cmdArray );
            try {
                    p.waitFor();
            } catch (InterruptedException e) {
                    //do nothing?!
            }
            logger.info( "Yices exection finished, processing results..." );
            
            // Retrieve results
            InputStream in = p.getInputStream();
            String yicesResult = read(in);
            logger.debug( "Retrieved result succussfully!" );
            in.close();
        
            // Create DecisionProcedureResult from Yices results
            boolean result = yicesResult.indexOf( YicesUnsatAnwser ) >= 0;
            return new DecisionProcedureResult( result, yicesResult, Constraint.BOTTOM );
            
        } catch( IOException e ) {
            logger.info( "An IOException occured:", e );
            final String errorMessage = 
                "\"Yices\" execution failed:\n\n" + e + "\n\n" +
                "To make use of Yices make sure that \n\n" + 
                "1. the binary is named yices "  +
                "2. the directory where the binary resides is in your $PATH variable\n" +
                "3. the binary has executable file permissions.";
            throw new RuntimeException( errorMessage );
        }
    }    
    
}
