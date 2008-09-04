package de.uka.ilkd.key.visualization;


import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.logic.op.SetAsListOfProgramMethod;
import de.uka.ilkd.key.logic.op.SetOfProgramMethod;
import de.uka.ilkd.key.proof.Node;


public class ExecutionTraceModel {

    public final static Integer TYPE1 = new Integer(1);
    public final static Integer TYPE2 = new Integer(2);
    public final static Integer TYPE3 = new Integer(3);
    
    
    protected TraceElement start=null;
    protected TraceElement end= null;
    private ContextTraceElement she=null;
    private Node startNode, endNode;
    private long rating=0;
    private boolean uncaughtException = false;
    private TraceElement exception=null; 
    private Integer type;
    private SimpleVisualizationStrategy.Occ startOcc;
    // indicates that the symbolic execution on this trace has terminated
    // (either normally or by an uncaught exception)
    private boolean terminated = false;
    
    public ExecutionTraceModel(TraceElement start, TraceElement end,
			       ContextTraceElement she,Node startN, Node endN){
        this.startNode= startN;
        this.endNode = endN;
        this.start=start;
	this.end = end;
	this.she = she;
        findUncaughtExeption();
    }

    public ExecutionTraceModel(TraceElement start, TraceElement end,
			       ContextTraceElement she, long rating, Node startN, Node endN, 
			       Integer type, SimpleVisualizationStrategy.Occ startOcc){
        this.startNode= startN;
        this.startOcc=startOcc;
        this.endNode = endN;
        this.start=start;
	this.end = end;
	this.she = she;
	this.rating = rating;
        this.type= type;
        findUncaughtExeption();
    }


    public Node  getFirstNode(){
        return startNode;
    }
    
    public Node  getLastNode(){
        return endNode;
    }     
    
    public TraceElement getFirstTraceElement(){
	return start;
    }

    public TraceElement getLastTraceElement(){
	return end;
    }

    public ContextTraceElement getLastContextTraceElement(){
	return she;
    }
    
    public void setLastContextTraceElement(ContextTraceElement she){
	this.she = she;
    }

    public long getRating(){
	return rating;
    }

    public void setTerminated(boolean terminated){
	this.terminated = terminated;
    }

    public boolean blockCompletelyExecuted(){
	return terminated;
    }

    private boolean noExecutableStatement(ProgramElement block){
	if(block instanceof StatementBlock){
	    StatementBlock sb = (StatementBlock) block;
	    return sb.isEmpty() || sb.getBody().size()==1 && 
		noExecutableStatement(sb.getBody().getStatement(0));
	}
	if(block instanceof MethodFrame){
	    return noExecutableStatement(((MethodFrame) block).getBody());
	}
	return false;
    }

    /**
     * Returns all ProgramMethods occuring in this trace.
     */
    public SetOfProgramMethod getProgramMethods(Services serv){
	SetOfProgramMethod result = SetAsListOfProgramMethod.EMPTY_SET;
	TraceElement current = start;
	while(current != end){
	    JavaASTCollector coll = 
		new JavaASTCollector(current.getProgram(), 
				     MethodFrame.class);
	    coll.start();
	    ListOfProgramElement l = coll.getNodes();
	    IteratorOfProgramElement it = l.iterator();
	    while(it.hasNext()){
		MethodFrame mf = (MethodFrame) it.next();
		if(mf.getProgramMethod() != null){
		    result = result.add(mf.getProgramMethod());
		}
	    }
	    current = current.getNextInProof();
//	    current = current.getNextExecuted();
	}
	return result;
    }

    public Set getExecutedStatementPositions(){
	HashSet result = new HashSet();
	TraceElement current = start;
	while(current != end){
	    if(current.getSrcElement()!=null){
		result.add(current.getSrcElement().
			   getPositionInfo().getStartPosition());
	    }
	    current = current.getNextInProof();
	}
	return result;
    }

    /**
     * Returns the first ExecutionContext occuring in this trace.
     */
    public TypeReference getOuterExecutionContext(){
	TraceElement current = start;
	while(current != end){
	    if(current.getExecutionContext() != null){
		return ((ExecutionContext)current.getExecutionContext()).
		    getTypeReference();
	    }
	    current = current.getNextExecuted();
	}
	return null;
    }
    
    /**
     * 
     * @param cte a ContextTraceElement in the Execution Trace Model
     * @return  the path to cte
     */
    public  ContextTraceElement[] getPath(ContextTraceElement cte){
        LinkedList parents = new LinkedList();
        ContextTraceElement parent;
        parent = cte.getParent();
        parents.add(cte);
        while (parent!=TraceElement.PARENTROOT){
	    parents.addFirst(parent);
	    parent=parent.getParent();
        }
        ContextTraceElement[] array = new ContextTraceElement[parents.size()]; 
        parents.toArray(array);
        return array;
    }
    

    private void findUncaughtExeption() {
        TraceElement che = getLastContextTraceElement();
        if (che !=null){
            while (che != TraceElement.END){
                if (che.getSrcElement() instanceof Throw) {
                    exception = che;
                    uncaughtException = true;
		    return;
		}
		che = che.getNextInProof();
	    }        
        }
    }

    public boolean uncaughtException(){
        return uncaughtException;
    }
    
    public TraceElement getUncaughtException(){
        return exception;
    }

    public ContextTraceElement getFirstContextTraceElement(){
	if (start instanceof ContextTraceElement) {
	    return (ContextTraceElement)start;
        }
        return start.getNextExecuted();
    }

    public Integer getType(){
        return type;
    }
    
    public SimpleVisualizationStrategy.Occ getStartOcc(){
        return startOcc;
    }

    public String toString(){
	String result = "";
	ContextTraceElement cte = getFirstContextTraceElement();
	while(cte != null){
	    result += toStringTree(cte, "   ");
	    if(cte instanceof ParentContextTraceElement){
		cte = ((ParentContextTraceElement) cte).stepOver();
	    }else{
		cte = cte.getNextExecuted();
	    }
	}
	return result;
    }

    public String toStringTree(ContextTraceElement cte, String indention){
	String result = toStringElement(cte, indention);
	if("".equals(result)){
	    return "";
	}
	if(cte instanceof ParentContextTraceElement){
	    ParentContextTraceElement pcte = (ParentContextTraceElement) cte;
	    ContextTraceElement[] children = pcte.getChildren();
	    for(int j=0; j<children.length; j++){
		result += toStringTree(children[j], indention+"  ");
	    }
	}
	return result;
    }

    public String toStringElement(ContextTraceElement cte, String indention){
	String result;
	if(cte == null) return "";
	if (cte.getContextStatement() != null) {
	    result = indention + cte.getContextStatement();
	} else if(cte.getSrcElement() != null){
	    result = indention + cte.getSrcElement();
	} else{
	    return "";
	}
	int i = result.indexOf("\n");
	if (i > -1) {
	    result = result.substring(0, i)+"\n";
	}else{
	    result += "\n";
	}
	return result;
    }
    
}
