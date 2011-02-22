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

import de.uka.ilkd.key.java.Services;






public interface SMTSolver {
    public enum ReasonOfInterruption{User,Timeout,Exception,NoInterruption};
    public enum SolverState{Waiting,Running,Stopped};


    
    /**
     * This solver's name.
     */
    public String name();

    
    /**
     * Returns an SMT translator which produces the format understood 
     * by this solver. 
     */
    public SMTTranslator getTranslator(Services services);    
    
    
   

    public SolverType getType();
    

   

    /**
     * Determines whether taclets are used for this solver.
     * @param b <code>true</code> if taclets should be used.
     */
    public void useTaclets(boolean b);

    
    public void interrupt(ReasonOfInterruption reasonOfInterruption);
    
    public void start(SolverTimeout timeout);
    
    public SolverTimeout getSolverTimeout();
    
    public long getStartTime();
    
    public long getTimeout();
    
    public SolverState getState();
    
    public boolean wasInterrupted();
    
     
    
    public ReasonOfInterruption getReasonOfInterruption();

    
    public SMTSolverResult getFinalResult();
    
    public void interrupt();
    
    
    
  
    
   
}
