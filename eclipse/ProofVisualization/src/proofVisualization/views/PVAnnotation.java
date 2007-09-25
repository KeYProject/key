/*
 * Created on 21.05.2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package proofVisualization.views;

import org.eclipse.jface.text.source.Annotation;

import de.uka.ilkd.key.visualization.TraceElement;
import de.uka.ilkd.key.visualization.ContextTraceElement;

/**
 * @author baum
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class PVAnnotation extends Annotation {
    TraceElement te;
    public PVAnnotation(String type, boolean isPersistent,TraceElement he, String message){
    	super(type,isPersistent,message);
    	this.te = he;
    }
    
    public static String getHoverMessage(ContextTraceElement he,String t){
    	String s="";//="SerialNr: "+he.serialNr()+"\n";
        s += "Executed: "+he.getNumberOfExecutions()+"\n";
        //if (t.equals("ProofVisualization.PVAnnotationType3"))
        //s += "Renamings: TODO";
        return s;
        
    }
    
	public TraceElement getTraceElement(){
     return te;   
    }
	
	public void setTraceElement(TraceElement he){
	    this.te = he;   
    }

}
