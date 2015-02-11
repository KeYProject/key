// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

/**
 * 
 */
package de.uka.ilkd.key.core;

import de.uka.ilkd.key.proof.Proof;

public class DefaultTaskFinishedInfo implements TaskFinishedInfo {

    private final Object source;
    
    // TODO
    // can be Throwable or ApplyStrategyInfo
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

    @Override
    public long getTime() {
        return time;
    }

    @Override
    public Object getResult() {
        return result;
    }

    @Override
    public Object getSource() {           
        return source;
    }

    @Override
    public int getAppliedRules() {
        return appliedRules;
    }

    @Override
    public int getClosedGoals() {
        return closedGoals;
    }

    @Override
    public Proof getProof() {            
        return proof;
    }       
    
    // display message for the status bar
    @Override
    public String toString() {
        if ( appliedRules != 0 ) {
            StringBuilder message = new StringBuilder();
            String timeString = (time/1000) + "." + ((time%1000)/100);

            message.append("Strategy: Applied ").append(appliedRules).append(" rule");
            if ( appliedRules != 1 ) {
                message.append("s");
            }
            message.append(" (").append(timeString).append(" sec), ");
            message.append(" closed ").append(closedGoals).append(" goal");
            if ( closedGoals != 1 ) {
                message.append("s");             
            }
            message.append(", ").append(proof.openGoals().size());
            message.append(" remaining");
            return message.toString();
        } else {
            return "No rules applied";
        }
    }
}