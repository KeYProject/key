// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.io.IOException;

import de.uka.ilkd.key.proof.decproc.JavaDecisionProcedureTranslationFactory;
import de.uka.ilkd.key.rule.*;

/** This class represents a standardized implementation of <tt>AbstractExecDecproc</tt>.
 *  <p>
 *  It checks the availability of a decision procedure by invoking it with one or zero command
 *  line arguments. Thereby a normal termination of execution is presumed, which, in most cases,
 *  can be reached by the use of a single command line argument.
 *  <p>
 *  All decicion procedures that can be treated in this way should be handled by this class
 *  <p>
 *  To modify the actual availability check, a hook for subclassing is provided by the
 *  <tt>isCurrentDecprocAvailable</tt> method
 *  @see #isCurrentDecprocAvailable(String, String)
 *  <p>
 *  
 * @author akuwertz
 * @version 1.0,  09/10/2006
 */

public class ConcreteExecDecproc extends AbstractExecDecproc {

    /* Attributes */
    
    /** <tt>Array</tt> containing the needed information for each decision procedure.
     * That is the name of executable, the argument to be handed over and the rule to create,
     * if the decision procedure is available */
    private static final Object[][] decisionProcedures = {
        /* If this class is extended by further decision procedures, this array also has to
           be extended properly */
        {   "Simplify", 
            "-help",
            new SimplifyIntegerRule( new JavaDecisionProcedureTranslationFactory() ) },
        { "ics", 
          "-help",
          new ICSIntegerRule( new JavaDecisionProcedureTranslationFactory() ) },
        { "cvcl",
          "-help",
          new CVCLiteIntegerRule( new JavaDecisionProcedureTranslationFactory() ) },
        { "cvc3",
          "-help",
          new CVC3IntegerRule( new JavaDecisionProcedureTranslationFactory() ) },
        { "yices",
          "--help",
          new YicesIntegerRule(new JavaDecisionProcedureTranslationFactory()) },
    };
    
    /** The command for the configured decision procedure to execute */
    protected final String cmd;
    /** The argument to be passed on execution */
    protected final String arg;
    /** The <tt>AbstractIntegerRule</tt> to be added to the <tt>ListOfBuiltInRule</tt>, if the
     * configured decision procedure is available */
    protected final AbstractIntegerRule rule;
        
    
    /** String constants representing error messages */
    private static final String noDecprocForIndex = 
        "No decision procedure exists for the given index!";
    private static final String internalError =
        "An internal error occured: Expected an object of type String in decisionProcedure" +
        " array at index ";
    private static final String internalErrorRule = 
        "An internal error occured: Expected an object of type Rule in decisionProcedure" +
        " array at index ";
    
    
    
    /* Constructors */
        
    /** Explicit constructor. Creates a new <tt>ConcreteExecDecproc</tt> configured with one the
     * internally stored decision procedures, choosen by the given integer index 
     * <tt>concreteDecproc</tt>
     *
     * @param concreteDecproc the integer index specifying the decision procedure this
     *                        <tt>ConcreteExecDecproc</tt> should be configured with
     */
    public ConcreteExecDecproc( int concreteDecproc ) {
        if ( concreteDecproc < 0  || concreteDecproc >= decisionProcedures.length ) 
            throw new IllegalArgumentException( noDecprocForIndex );
        Object helper = decisionProcedures[ concreteDecproc ][ 0 ];
        if ( helper instanceof String ) cmd = (String) helper;
        else throw new RuntimeException( internalError + concreteDecproc ); 
        helper = decisionProcedures[ concreteDecproc ][ 1 ];
        if ( helper instanceof String ) arg = (String) helper;
        else throw new RuntimeException( internalError + concreteDecproc );
        helper = decisionProcedures[ concreteDecproc ][ 2 ];
        if ( helper instanceof AbstractIntegerRule ) rule = (AbstractIntegerRule) helper;
        else throw new RuntimeException( internalErrorRule + concreteDecproc );
    }
    
    
    
    /* Public and private methods */
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.AbstractExecDecproc#isAvailable()
     */
    public boolean isAvailable() {
        return isCurrentDecprocAvailable( cmd, arg );
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.AbstractExecDecproc#getRule()
     */
    public AbstractIntegerRule getRule() {
        return rule;
    }
    
    
    /** Returns the command for the configured decision procedure
     * @return the command <tt>String </tt>for the configured decision procedure
     */
    public String getCmd() {
        return cmd;
    }
    
    
    /** Returns the number of elements in the decision procedure array 
     * @return the number of elements in the decision procedure array
     */
    public static int getDecprocNumber() {
        return decisionProcedures.length;
    }
    
    
    /** Checks if the given <tt>decisionProcedure</tt> is available by executing it with
     * the given <tt>argument</tt>.<br>
     * If the decision procedure does not terminate normally before a given timeout, it will 
     * be regarded as not available.
     * <p>
     * This method is protected so that subclasses can use it as a hook for doing a
     * modified availability check
     *
     * @param decisionProcedure the String with the name of the executable
     * @param argument  a String to be handed over as an argument (in order to ensure
     *                    normal termination of the procedure, e.g. Simplify would wait
     *                    for input and not terminate)
     * @return <tt>true</tt> if the decision procedure was found and could be executed properly
     */
     protected boolean isCurrentDecprocAvailable( final String decisionProcedure,
                                                    final String argument) {
        boolean available = false;
        Process process = null;
        try {
            process = Runtime.getRuntime().exec(
                    new String[] { decisionProcedure, argument });

            long start = System.currentTimeMillis();

            while (System.currentTimeMillis() - start < TIMEOUT) {
                try {
                    available = process.exitValue() == 0;
                } catch (IllegalThreadStateException itse) {
                    // process has not terminated yet
                    available = false;
                    continue;
                }
                break;
            }
        } catch (IOException e) {
            available = false;
        }

        return available;
    }
    
}
