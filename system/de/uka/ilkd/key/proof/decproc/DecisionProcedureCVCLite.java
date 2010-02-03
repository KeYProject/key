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

import java.io.IOException;
import java.io.InputStream;
import org.apache.log4j.Logger;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.proof.Goal;

/** This class is responsible for invoking the back-end decision procedure CVCLite on a
 * <tt>Benchmark</tt>, evaluating its results and returning them represented properly to 
 * <tt>DecisionProcedureSmtAuflia</tt>
 * 
 * @author akuwertz
 * @version 1.0,  05/08/2006
 */

public class DecisionProcedureCVCLite extends DecisionProcedureSmtAuflia {

    /** A <tt>String</tt> representation of the command used to execute CVCLite */
    private static final String CVCLiteCommand = "cvcl";
    /** <tt>String</tt>s representing the CVCLite command option for SMT-LIB support */ 
    private static final String CVCLiteSmtFlag1 = "-lang";
    private static final String CVCLiteSmtFlag2 = "smtlib";
    /** A <tt>String</tt> representing the answer of CVCLite if it found a benchmark to be 
     * unsatisfiable */
    private static final String CVCLiteUnsatAnwser = "Unsatisfiable";
    
    /** A <tt>Logger</tt> for monitoring and logging of progress in the decision procedure */
    private static final Logger 
        logger = Logger.getLogger( DecisionProcedureCVCLite.class.getName() );
    // Logger is created hierarchical to inherit configuration and behaviour from parent
    
    
    /** A mere constructor.
     * 
     * @param goal the <tt>Goal</tt> which should be checked for satisfiability
     * @param dptf the <tt>DecisionProcedureTranslationFactory</tt> used to ranslate the the
     *             sequent of the goal
     * @param services the <tt>Services</tt> used during the translation process 
     */
    public DecisionProcedureCVCLite( Goal goal, DecisionProcedureTranslationFactory dptf,
                                     Services services) {
        super(goal, dptf, services);
    }

    
    /** This method is reponsible executing and evaluating CVCLite. It implements the hook provided in 
     * <tt>DecisionProcedureSmtAuflia</tt>
     * 
     *  @throws RuntimeException if an <tt>Exception</tt> occured due to the invocation or 
     *                           execution of CVCLite
     */
    protected DecisionProcedureResult execDecProc() {
    
        try {
            // Run CVCLite on stored translation result (benchmark)
            logger.info( "Running CVCLite on created benchmark..." );
            String[] cmdArray = { CVCLiteCommand , CVCLiteSmtFlag1, CVCLiteSmtFlag2,
                                  super.getTempFile().getPath() };
            Process p = Runtime.getRuntime().exec( cmdArray );
            logger.info( "CVCLite exection finished, processing results..." );
            
            // Retrieve results
            InputStream in = p.getInputStream();
            String cvcResult = read(in);
            logger.debug( "Retrieved result succussfully!" );
            in.close();
        
            // Create DecisionProcedureResult from CVCLite results
            boolean result = cvcResult.indexOf( CVCLiteUnsatAnwser ) >= 0;
            return new DecisionProcedureResult( result, cvcResult, Constraint.BOTTOM );
            
        } catch( IOException e ) {
            logger.info( "An IOException occured:", e );
            final String errorMessage = 
                "\"CVCLite\" execution failed:\n\n" + e + "\n\n" +
                "Currently, CVCLite supports only Linux operated systems!\n\n" +
                "To make use of CVCLite make sure that \n\n" + 
                "1. the main shell script is named cvcl.sh\n"  +
                "2. the directory where the shell script resides is in your $PATH variable\n" +
                "3. the shell script and the binary have executable file permissions.";
            throw new RuntimeException( errorMessage );
        }
    }    
    
}
