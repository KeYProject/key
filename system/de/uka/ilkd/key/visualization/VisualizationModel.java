// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.visualization;

import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedList;

import de.uka.ilkd.key.proof.Node;

public class VisualizationModel {
    ExecutionTraceModel[] traces;
    Node node = null;
    static Comparator comp = new TraceComparator();


    public VisualizationModel(Node node,ExecutionTraceModel[] traces){
	this.traces = traces;
	this.node = node;
	if (traces!=null)
            Arrays.sort(this.traces,comp);
    }

    public Node getNode(){
	return node;
    }

    public ExecutionTraceModel[] getExecutionTraces(){
	return traces;
    }
    
    /**
     * @return the Execution Trace Models that contain ContextTraceElements and
     *         that are of type 1
     */    
    public ExecutionTraceModel[] getInterestingExecutionTraces() {
        LinkedList result = new LinkedList();
        for (ExecutionTraceModel trace : traces) {
            if ((trace.getFirstContextTraceElement() != TraceElement.END) &&
                    trace.getType() == ExecutionTraceModel.TYPE1) {
                result.add(trace);
            }
        }
        ExecutionTraceModel[] exTraceModels = new ExecutionTraceModel[result
                .size()];
        result.toArray(exTraceModels);
        return exTraceModels;
    }

    
   
    /**
     * @return true if t1 is more useful to understand the proof then t2
     */

    public boolean compare(ExecutionTraceModel t1, ExecutionTraceModel t2){
	if  (t1.getRating()>t2.getRating())
	    return true;
	else if (t1.getRating()==t2.getRating()) 
	    return t1.getFirstTraceElement().serialNr()>t2.getFirstTraceElement().serialNr();
	return false;
    }

	
    public static  class TraceComparator implements Comparator{
	public int compare (Object o1, Object o2){
	    ExecutionTraceModel t1 = (ExecutionTraceModel) o1;
	    ExecutionTraceModel t2 = (ExecutionTraceModel) o2;
	    if 	 (t1.getRating()==t2.getRating()) return 0;
	    else if  (t1.getRating()<t2.getRating()) return 1;
	    return -1;

	}

	public boolean equals(Object o1, Object o2){
	    ExecutionTraceModel t1 = (ExecutionTraceModel) o1;
	    ExecutionTraceModel t2 = (ExecutionTraceModel) o2;	    
	    return  (t1.getRating()==t2.getRating());
	}

    }
	    

}
