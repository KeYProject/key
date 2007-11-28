// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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

import de.uka.ilkd.key.rule.AbstractIntegerRule;

/** This abstract superclass enables unified checking for the availability of external decision
 *  procedure executables. The availability is hereby checked by a test execution of the
 *  decision procedure of interest.<br>
 *  If a decision procedure is available, an <tt>AbstractIntegerRule</tt> (representing the
 *  execution of this decision procedure) can be added to a list of available rules. 
 * 
 * @author akuwertz
 * @version 1.0,  09/10/2006
 */

public abstract class AbstractExecDecproc {
    
    /** Maximum time to wait for decision procedure answer in ms */
    protected static final long TIMEOUT = 5000;

    
    
    /** Checks whether a specified decision procedure is available for execution
     * @return <tt>true</tt> if the specified decision procedure is available
     */
    public abstract boolean isAvailable();

    
    /** Returns an integer rule representing the execution of the specified decision procedure
     * @return an <tt>AbstractIntegerRule</tt> representing the specified decision procedure
     */
    public abstract AbstractIntegerRule getRule();
        
    
    /** Returns the command string used to execute the specified decision procedure
     * @return the <tt>String</tt> used to execute the decision procedure
     */
    public abstract String getCmd();
}
