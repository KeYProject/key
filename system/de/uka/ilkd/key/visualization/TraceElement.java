// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualization;


import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.inst.ContextInstantiationEntry;

public class TraceElement {

    protected TraceElement nextInProof;
    protected ContextTraceElement stepInto;
    protected SourceElement programElement;
    protected IExecutionContext executionContext;
    protected Node node;
    protected ProgramElement program;
    protected PosInOccurrence posOfModality;
    
    static public final ContextTraceElement END = new ContextTraceElement();
    static public final ParentContextTraceElement PARENTROOT = new ParentContextTraceElement();

    public TraceElement(SourceElement prElement, Node node, TraceElement nip, ContextTraceElement ne){
	this(prElement, node, nip, ne, null);
    }

    public TraceElement(SourceElement prElement, Node n,  TraceElement nip, ContextTraceElement ne, IExecutionContext exCont){
	node = n;
	posOfModality = n.getAppliedRuleApp().posInOccurrence();
        nextInProof = nip;
	stepInto = ne;
	programElement = prElement;
	executionContext = exCont;
        ContextInstantiationEntry cie = ((PosTacletApp) n.getAppliedRuleApp())
                .instantiations().getContextInstantiation();
        program = (cie.contextProgram());
    }

    public TraceElement(){
	nextInProof = this;
    }


    public PosInOccurrence getPosOfModality(){
        return posOfModality;
    }
    
    public ProgramElement getProgram(){
        return program;
    }
    
    public SourceElement getSrcElement(){
	return programElement;
    }

    public TraceElement getNextInProof(){
	return nextInProof;
    }

    public ContextTraceElement getNextExecuted(){
	return stepInto;
    }

    public IExecutionContext getExecutionContext(){
	return executionContext;
    }


    public void setExecutionContext(IExecutionContext con){
	executionContext = con;
    }


    public void setNextInProof(TraceElement he){
	nextInProof=he;
    }

    public void setStepInto(ContextTraceElement he){
	stepInto=he;
    }

    public int serialNr(){
	if (node==null) return -1;
	return node.serialNr();
    }
    
  /*  public ProgramElement getProgram(){
        return posOfModality.subTerm().executableJavaBlock().program();
    }*/


    public Node node(){
	return node;
    }

    public String toString(){
	String s ="TraceElement:\n";
	if  (this == END) return "END";
	if  (this == PARENTROOT) return "PARENTROOT";
	if (node!=null) s = s+(serialNr()+"\n");
	if (programElement!=null) s=s+programElement;
	if (stepInto!=null) s= s+ "\nNext executed: "+stepInto.serialNr();
	return s;
    }

}
