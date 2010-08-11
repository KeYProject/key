// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.smt;

/**This interface was introduced to minimize redundant code for handling the process of showing the progress. 
 * Both SMTRule and SMTRuleMulti should implement this interface to have the same basis for showing the current progress.
 */
public interface MakesProgress {
   
   /** Adds a <code>ProgressMonitor</code> to the set of progress listener.*/
   public void addProgressMonitor(SMTProgressMonitor p);
    
    /**
     * Removes a <code>ProgerssMonitor</code> from the set of progress listener.
     * @param p the ProgressMonitor to remove.
     * @return true, if the method has succeeded.
     */
    public boolean removeProgressMonitor(SMTProgressMonitor p);
    
    /**
     * Removes all ProgressMonitors from the set of progress listener.
     */
    public void removeAllProgressMonitors();
	
    
    /**
     * Calling the method <code>interrupt()</code> causes the interruption of the current process. 
     */
    public void interrupt();
    
    public String getTitle();

}
