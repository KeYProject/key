// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/**
 * 
 */
package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.proof.Proof;

public class DefaultTaskFinishedInfo implements TaskFinishedInfo {

    private final Object source;
    private final Object result;
    private final Proof proof;
    private final long time;
    private final int appliedRules;
    private final int closedGoals;
    
    
    public DefaultTaskFinishedInfo(Object source, Object result,
            Proof proof, long time, 
            int appliedRules, int closedGoals) {
        this.source = source;
        this.result = result;
        this.proof = proof;
        this.time = time;
        this.appliedRules = appliedRules;
        this.closedGoals = closedGoals;
    }

    public long getTime() {
        return time;
    }
    
    public Object getResult() {
        return result;
    }
    
    public Object getSource() {           
        return source;
    }

    public int getAppliedRules() {
        return appliedRules;
    }

    public int getClosedGoals() {
        return closedGoals;
    }

    public Proof getProof() {            
        return proof;
    }        
}
