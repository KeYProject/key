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
     *        the external solver, in seconds. If the time is exceeded, UNKNOWN 
     *        is returned.
     * @throws IOException if the external prover could not be found, executed or if the SMT translation
     * could not be written to a file
     */
    public SMTSolverResult run(String formula, int timeout, Services services) throws IOException;

    
    /**
     * Check if the given goal is valid.
     * @param goal The goal to be proven.
     * @param timeout The maximum time that should be used to execute 
     *        the external solver, in seconds. If the time is exceeded, UNKNOWN 
     *        is returned.
     * @throws IOException if the external prover could not be found, executed or if the SMT translation
     * could not be written to a file
     */
    public SMTSolverResult run(Goal goal, int timeout, Services services) throws IOException;
    

    /**
     * Check if the given formula is valid.
     * @param formula The formula to be proven.
     * @param timeout The maximum time that should be used to execute 
     *        the external solver, in seconds. If the time is exceeded, UNKNOWN 
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
}
