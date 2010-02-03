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


import java.util.ArrayList;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.proof.Node;

public class ParentContextTraceElement extends ContextTraceElement {

    private ContextTraceElement stepOver;

    public ParentContextTraceElement(SourceElement prElement, Node n, TraceElement nip, 
				      ContextTraceElement ne, ContextTraceElement nsl){
	super(prElement, n, nip, ne);
	stepOver = nsl;
    }

    public ParentContextTraceElement(SourceElement prElement, Node n,  TraceElement nip, 
				      ContextTraceElement ne, ContextTraceElement nsl, IExecutionContext exCont){
	super(prElement, n, nip, ne,exCont);
	stepOver = nsl;
    }

    public ParentContextTraceElement(){
	nextInProof = this;
	stepInto = this;
	stepOver = this;
    }

    public void setStepOver(ContextTraceElement he){
	stepOver = he;
    }

    public ContextTraceElement stepOver(){
	return stepOver;
    }

    
    public ContextTraceElement[] getChildren() {
	ArrayList children = new ArrayList();
        ContextTraceElement che = getNextExecuted();
        while ((che!=TraceElement.END)&& this.equals(che.getParent())){
	    children.add(che);
	    if (che instanceof ParentContextTraceElement) 
		che= ((ParentContextTraceElement)che).stepOver();
	    else che= che.getNextExecuted();
        }
	ContextTraceElement[] result = new ContextTraceElement[children.size()];
	children.toArray(result);
        return result;
    }


    public String toString(){
	String s ="ParentContextTraceElement:\n";
	if  (this == END) return "END";
	if  (this == PARENTROOT) return "PARENTROOT";
	if (node != null) s = s+(serialNr()+"\n");
	if (programElement != null) s=s+programElement+"\n"+programElement.getPositionInfo();
	if (stepInto != null) s = s+ "\nStep Into: "+stepInto.serialNr();
	if (stepOver != null) s = s+"\nStep Over: "+stepOver.serialNr();
	if (getParent()!=null) s = s+"\nParent: "+getParent().serialNr();
	return s;
    }

}
