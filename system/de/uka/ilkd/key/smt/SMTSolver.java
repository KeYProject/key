//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import java.io.IOException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.ProgressMonitor;


public interface SMTSolver {
    
    /**
     * This solver's name.
     */
    public String name();

    
    /**
     * Returns an SMT translator which produces the format understood 
     * by this solver. 
     */
    public SMTTranslator getTranslator(Services services);    
    
    
    /**
     * Check if the given formula is valid. The formula must already
     * be a string in the expected format for this solver, e.g. as produced by
     * the translator returned by getTranslator(). For a higher-level interface
     * (strongly recommended), use one of the other run() methods.
     * @param formula The formula to be proven.
     * @param timeout The maximum time that should be used to execute 
     *        the external solver, in ,illiseconds. If the time is exceeded, UNKNOWN 
     *        is returned.
     * @throws IOException if the external prover could not be found, executed or if the SMT translation
     * could not be written to a file
     */
    public SMTSolverResult run(String formula, int timeout, Services services) throws IOException;

    
    /**
     * Check if the given goal is valid.
     * @param goal The goal to be proven.
     * @param timeout The maximum time that should be used to execute 
     *        the external solver, in milliseconds. If the time is exceeded, UNKNOWN 
     *        is returned.
     * @throws IOException if the external prover could not be found, executed or if the SMT translation
     * could not be written to a file
     */
    public SMTSolverResult run(Goal goal, int timeout, Services services) throws IOException;
    

    /**
     * Check if the given formula is valid.
     * @param formula The formula to be proven.
     * @param timeout The maximum time that should be used to execute 
     *        the external solver, in milliseconds. If the time is exceeded, UNKNOWN 
     *        is returned.
     * @throws IOException if the external prover could not be found, executed or if the SMT translation
     * could not be written to a file
     */
    public SMTSolverResult run(Term formula, int timeout, Services services) throws IOException;
    
    /**
     * check, if this solver is installed and can be used.
     * @param recheck if false, the solver is not checked again, if a cached value for this exists.
     * @return true, if it is installed.
     */
    public boolean isInstalled(boolean recheck);
    
    /**
     * @return the command used for execution of the programm on default
     */
    public String getDefaultExecutionCommand();
    
    /**
     * add a monitor to watch the Progress in the execution.
     * During execution, all registered monitors are set to values between 0 and 99.
     * @param p
     */
    public void addProgressMonitor(ProgressMonitor p);
    
    /**
     * remove a registered progress monitor.
     * @param p
     * @return true, if remove was successful.
     */
    public boolean removeProgressMonitor(ProgressMonitor p);
    
    /**
     * remove all registered progress monitors.
     *
     */
    public void removeAllProgressMonitors();
    
    /**
     * 
     * @return the progress made on the current task. Value 0..99
     */
    public int getProgress();
    
    /**
     * interrupt a running SMT solver.
     */
    public void interrupt();
}
