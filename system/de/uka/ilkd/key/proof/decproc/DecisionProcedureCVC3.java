// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//Universitaet Koblenz-Landau, Germany
//Chalmers University of Technology, Sweden

//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.



package de.uka.ilkd.key.proof.decproc;

import java.io.IOException;
import java.io.InputStream;
import org.apache.log4j.Logger;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.proof.Goal;

/** This class is responsible for invoking the back-end decision procedure CVC3 on a
 * <tt>Benchmark</tt>, evaluating its results and returning them represented properly to 
 * <tt>DecisionProcedureSmtAuflia</tt>
 */

public class DecisionProcedureCVC3 extends DecisionProcedureSmtAuflia {

    /** A <tt>String</tt> representation of the command used to execute CVC3 */
    private static final String CVC3Command = "cvc3";
    /** <tt>String</tt>s representing the CVC3 command option for SMT-LIB support */ 
    private static final String CVC3SmtFlag1 = "-lang";
    private static final String CVC3SmtFlag2 = "smt";
    /** A <tt>String</tt> representing the answer of CVC3 if it found a benchmark to be 
     * unsatisfiable */
    private static final String CVC3UnsatAnwser = "unsat";

    /** A <tt>Logger</tt> for monitoring and logging of progress in the decision procedure */
    private static final Logger 
    logger = Logger.getLogger( DecisionProcedureCVC3.class.getName() );
    // Logger is created hierarchical to inherit configuration and behaviour from parent


    /** A mere constructor.
     * 
     * @param goal the <tt>Goal</tt> which should be checked for satisfiability
     * @param dptf the <tt>DecisionProcedureTranslationFactory</tt> used to ranslate the the
     *             sequent of the goal
     * @param services the <tt>Services</tt> used during the translation process 
     */
    public DecisionProcedureCVC3( Goal goal, DecisionProcedureTranslationFactory dptf,
            Services services) {
        super(goal, dptf, services);
    }


    /** This method is reponsible executing and evaluating CVC3. It implements the hook provided in 
     * <tt>DecisionProcedureSmtAuflia</tt>
     * 
     *  @throws RuntimeException if an <tt>Exception</tt> occured due to the invocation or 
     *                           execution of CVC3
     */
    protected DecisionProcedureResult execDecProc() {

        try {
            // Run CVC3 on stored translation result (benchmark)
            logger.info( "Running CVC3 on created benchmark..." );
            String[] cmdArray = { CVC3Command , CVC3SmtFlag1, CVC3SmtFlag2,
                    super.getTempFile().getPath() };
            Process p = Runtime.getRuntime().exec( cmdArray );
            logger.info( "CVC3 exection finished, processing results..." );

            // Retrieve results
            InputStream in = p.getInputStream();
            String cvcResult = read(in);
            logger.debug( "Retrieved result succussfully!" );
            in.close();

            // Create DecisionProcedureResult from CVC3 results
            boolean result = cvcResult.indexOf( CVC3UnsatAnwser ) >= 0;
            return new DecisionProcedureResult( result, cvcResult, Constraint.BOTTOM );

        } catch( IOException e ) {
            logger.info( "An IOException occured:", e );
            final String errorMessage = 
                "\"CVC3\" execution failed:\n\n" + e + "\n\n" +
                "Currently, CVC3 supports only Linux operated systems!\n\n" +
                "To make use of CVC3 make sure that \n\n" + 
                "1. the main shell script is named cvcl.sh\n"  +
                "2. the directory where the shell script resides is in your $PATH variable\n" +
                "3. the shell script and the binary have executable file permissions.";
            throw new RuntimeException( errorMessage );
        }
    }    

}

