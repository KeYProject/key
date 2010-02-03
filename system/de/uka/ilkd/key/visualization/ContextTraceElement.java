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


import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.proof.Node;

public class ContextTraceElement extends TraceElement {

    private ParentContextTraceElement  parent;
    protected int noe =-1;
    protected String label;
    protected SourceElement contextStatement = null;

    public ContextTraceElement(SourceElement prElement, Node node, TraceElement nip, ContextTraceElement ne){
	this(prElement, node, nip, ne, null);
    }

    public ContextTraceElement(SourceElement prElement, Node n,  TraceElement nip, ContextTraceElement ne, IExecutionContext exCont){
	super(prElement,n,nip,ne,exCont);
    }

    public ContextTraceElement(){
	super();
    }

    public void setContextStatement(SourceElement se){
	contextStatement = se;
    }

    public SourceElement getContextStatement(){
	return contextStatement;
    }

    public void setParent(ParentContextTraceElement he){
        parent = he;
    }

    public ParentContextTraceElement getParent(){
        return parent;
    }

    
    public int getNumberOfExecutions(){
	return noe;
    }

    public void setNumberOfExecutions(int noe){
	this.noe = noe;
    }

    public void setLabel(String s){
	label = s;
    }


    public String getLabel(){
	return label;
    }

   public String toString(){
	String s ="ContextTraceElement:\n";
	if  (this == END) return "END";
	if  (this == PARENTROOT) return "PARENTROOT";
	if (node!=null) s = s+(serialNr()+"\n");
	if (programElement!=null) s=s+programElement+"\n"+programElement.getPositionInfo();
	if (stepInto!=null) s= s+ "\nNext executed: "+stepInto.serialNr();
	if (parent!=null)s = s+"\nParent: "+parent.serialNr();
        return s;
    }

  

}
