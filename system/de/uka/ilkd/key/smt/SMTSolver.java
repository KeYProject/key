// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.smt;


import java.util.Collection;
import java.util.LinkedList;

import de.uka.ilkd.key.java.Services;

import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.SolverSession.InternResult;


public interface SMTSolver extends de.uka.ilkd.key.smt.launcher.Process {
    
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
     * Interpret the answer of the program.
     * This is very solverdepending. Usually, an exitcode of 0 inicates no error.
     * But not every solver returns 0 if successfull termination was reached.
     * @param output the String answered by the external programm.
     * @param error the String answered as error
     * @param exitstatus the status of the exit
     * @return A SMTSolverResult containing all information of the interpretation.
     * @throws IllegalArgumentException If the solver caused an error.
     */
    public SMTSolverResult interpretAnswer(String output, String error, int exitstatus) throws IllegalArgumentException;
    
    
    
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
    
    public String getExecutionCommand();
    
    public boolean useForMultipleRule();
    
    /**
     * @return Returns some information for the solver. If no information
     * is provided an empty String is returned. 
     */
    String getInfo();
    

    /**
     * Determines whether taclets are used for this solver.
     * @param b <code>true</code> if taclets should be used.
     */
    public void useTaclets(boolean b);
    
    public void prepareSolver(LinkedList<InternResult> goals, Services services, Collection<Taclet> taclets);
}
