// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.visualdebugger;

import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.proof.IteratorOfNode;
import de.uka.ilkd.key.proof.ListOfNode;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.SLListOfNode;

public class BreakpointManager {
    private LinkedList bp = new LinkedList();

    private boolean noEx = false;

    private ListOfNode st = SLListOfNode.EMPTY_LIST;

    private VisualDebugger vd;

    public BreakpointManager(VisualDebugger vd) {
        this.vd = vd;
    }

    public boolean addBreakpoint(Breakpoint b) {
        if (containsBp(b.getId()))
            return false;
        bp.add(b);
        return true;
    }

    public boolean containsBp(SourceElementId id) {
        Iterator it = bp.iterator();
        while (it.hasNext()) {
            SourceElementId currentId = ((Breakpoint) it.next()).getId();
            if (currentId.equals(id))
                return true;
        }
        return false;
    }

    public Object[] getBreapoints() {
        return bp.toArray();
    }

    public ListOfNode getSteps() {
        return st;
    }

    public boolean isNoEx() {
        return noEx;
    }

    private String print(ListOfNode lon) {
        IteratorOfNode it = lon.iterator();
        String result = "";
        while (it.hasNext()) {
            result += it.next().serialNr() + " ";
        }
        return result;
    }

    public void remove(Breakpoint b) {
        bp.remove(b);
    }

    public void setNoEx(boolean noEx) {
        // System.out.println("noEx set to "+noEx);
        this.noEx = noEx;
    }

    public boolean suspend(Node n, SourceElementId id) {
        return suspendByBreakpoint(id) || suspendByStep(n, id)
                || suspendByStepOver(n, id);
    }

    public boolean suspendByBreakpoint(SourceElementId id) {
        if (this.containsBp(id))
            return true;
        return false;
    }

    public boolean suspendByStep(Node n, SourceElementId id) {
        if (n.parent() != null) {
            return n.parent().getNodeInfo().getVisualDebuggerState()
                    .getStatementIdcount() == 0;
        }
        return false;
    }

    public boolean suspendByStepOver(Node n, SourceElementId id) {
        final VisualDebuggerState visualDebuggerState = n.getNodeInfo()
                .getVisualDebuggerState();
        final boolean suspendedSO = visualDebuggerState.getStepOver() != -1
                && n.serialNr() != visualDebuggerState.getStepOverFrom()
                && VisualDebugger.getVisualDebugger().getMethodStackSize(n) <= n
                        .parent().getNodeInfo().getVisualDebuggerState()
                        .getStepOver();
        return suspendedSO;
    }

    public String toString() {
        return "Steps: " + print(st) + "    BPs" + this.bp.toString()
                + "   NoEx " + this.noEx;
    }
}
