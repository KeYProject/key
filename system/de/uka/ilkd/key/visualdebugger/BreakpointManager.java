package de.uka.ilkd.key.visualdebugger;

import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.proof.IteratorOfNode;
import de.uka.ilkd.key.proof.ListOfNode;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.SLListOfNode;

public class BreakpointManager {
    private LinkedList bp=new LinkedList();

    private ListOfNode st = SLListOfNode.EMPTY_LIST;
    private VisualDebugger vd;
    private boolean noEx=false;

    public BreakpointManager(VisualDebugger vd){
        this.vd=vd;
    }

    public boolean suspendByBreakpoint(SourceElementId id){
        if (this.containsBp(id))
            return true;
        return false;
    }

    public boolean containsBp(SourceElementId id){
        Iterator it = bp.iterator();
        while(it.hasNext()){
            SourceElementId currentId= ((Breakpoint) it.next()).getId();
            if (currentId.equals(id))
                return true;
        }
        return false;
    }

    public boolean addBreakpoint(Breakpoint b){
        if (containsBp(b.getId()))
            return false;
        bp.add(b);
        return true;
    }

    public Object[] getBreapoints(){
        return bp.toArray();
    }

    public void remove (Breakpoint b){
        bp.remove(b);
    }


    public ListOfNode getSteps(){
        return st;
    }

    private String print(ListOfNode lon){
        IteratorOfNode it = lon.iterator();
        String result= "";
        while(it.hasNext()){
            result += it.next().serialNr()+" ";
        }
        return result;
    }


    public boolean suspendByStep(Node n, SourceElementId id){  
        if (n.parent() != null) {
            return n.parent().getNodeInfo().getVisualDebuggerState().getStatementIdcount()==0;
        } 
        return false;
    }

    public boolean suspendByStepOver(Node n, SourceElementId id) {   
        final VisualDebuggerState visualDebuggerState = 
            n.getNodeInfo().getVisualDebuggerState();
        final boolean suspendedSO = visualDebuggerState.getStepOver()!=-1 &&
        n.serialNr()!=visualDebuggerState.getStepOverFrom() &&
        VisualDebugger.getVisualDebugger().getMethodStackSize(n)<=n.parent().getNodeInfo().getVisualDebuggerState().getStepOver();                
        return suspendedSO;
    }


    public boolean suspend(Node n, SourceElementId id){
        return suspendByBreakpoint(id) || suspendByStep(n,id) || suspendByStepOver(n,id);
    }

    public boolean isNoEx() {
        return noEx;
    }

    public void setNoEx(boolean noEx) {
        //  System.out.println("noEx set to "+noEx);
        this.noEx = noEx;
    }

    public String toString(){        
        return "Steps: "+print(st)+"    BPs"+this.bp.toString()+ "   NoEx "+
        this.noEx ;
    }
}
