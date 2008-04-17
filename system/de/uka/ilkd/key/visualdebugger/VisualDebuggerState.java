// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger;

import java.util.HashMap;

import de.uka.ilkd.key.logic.PosInOccurrence;


/**
 * This class encapsulates some information which has been originally attached to 
 * node. As after three further add-ons made this way, Node would become unreadable
 * they are now collected here and PRELIMINARY attached to NodeInfo. The storage of these
 * objects have to be removed from there too. One has either to maintain a separate 
 * Node <-> VisualDebuggerState mapping in the visualdebugger package (attention: you have to 
 * keep track of added and _removed_ nodes in order to avoid memory leaks)
 * or one has to add a general framework in order to attach additional infos on proof 
 * nodes. 
 */
public class VisualDebuggerState {

    private HashMap<PosInOccurrence, Label> labels = new HashMap<PosInOccurrence, Label>();

    private boolean looking = false;

    private int statementIdcount = -1;

    private int stepOver = -1;

    private int stepOverFrom = -1;

    
    public VisualDebuggerState() {
        
    }    
    
    // ALL methods below are for the eclipse symbolic debugger plug-in
    // THEY HAVE TO BE MOVED OUT TO THE DEBUGGER package
    // where a separate mapping node <-> debugger status has to be maintained    
    public HashMap<PosInOccurrence, Label> getLabels() {
        return this.labels;
    }

    public int getStatementIdcount() {
        return this.statementIdcount;
    }

    public int getStepOver() {
        return this.stepOver;
    }
    
    public int getStepOverFrom() {
        return stepOverFrom;
    }

    public boolean isLooking() {
        return looking;
    }

    public void setLabels(HashMap<PosInOccurrence, Label> labels) {
        this.labels = labels;
    }

    public void setLooking(boolean looking) {
        this.looking = looking;
    }

    public void setStatementIdcount(int statementIdcount) {
        this.statementIdcount = statementIdcount;
    }

    public void setStepOver(int stepOver) {
        this.stepOver = stepOver;
    }

    public void setStepOverFrom(int stepOverFrom) {
        this.stepOverFrom = stepOverFrom;
    }
    
}
