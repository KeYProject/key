// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.proof.Goal;

public interface SMTProgressMonitor {
    public final static int MAX_TIME = 1000;

    public enum SolveType {UNKOWN,SOLVABLE,UNSOLVABLE};
    
    public void setTimeProgress(String title, long time);
    public void setTimeMaximum(int maximum);
    public void setGoalProgress(Goal goal, SolveType type);  
    public void setGoalMaximum(int maximum);
    public void exceptionOccurred(String text, Exception e);    
}	
