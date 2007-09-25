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
import de.uka.ilkd.key.rule.AbstractIntegerRule;
import de.uka.ilkd.key.rule.SVCIntegerRule;

/** This class checks if the external decision procedure SVC is available.
 * <p>
 * If therefore creates a new process and passes data, formatted as an SMT-Lib Benchmark,
 * to its input stream. If svc is available, it will terminate normally. (Without passing
 * syntactically correct data, it won't terminate normally
 * 
 * @author akuwertz
 * @version 1.0,  09/11/2006
 */

public class ExecSVC extends AbstractExecDecproc {

    /** The command used to execute SVC */
    private static final String cmd = "svc";
    
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.AbstractExecDecproc#isAvailable()
     */
    public boolean isAvailable() {
        String benchmark = "(benchmark test :logic QF_AUFLIA :formula false)";
        boolean available = false;
        Process process = null;
        try {
            process = Runtime.getRuntime().exec( cmd );
            process.getOutputStream().write( benchmark.getBytes() );
			process.getOutputStream().close();
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
    

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.AbstractExecDecproc#getRule()
     */
    public AbstractIntegerRule getRule() {
        return new SVCIntegerRule( new JavaDecisionProcedureTranslationFactory() );
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.AbstractExecDecproc#getCmd()
     */
    public String getCmd() {
        return cmd;
    }
}
