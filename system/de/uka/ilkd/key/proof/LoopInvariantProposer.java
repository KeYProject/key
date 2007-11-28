// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.annotation.Annotation;
import de.uka.ilkd.key.java.annotation.LoopInvariantAnnotation;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.*;
import de.uka.ilkd.key.rule.*;

public class LoopInvariantProposer implements InstantiationProposer {

    /**
     * An instance of LoopInvariantProposer
     */
    public static final LoopInvariantProposer DEFAULT = new LoopInvariantProposer();

    
    /**
     * Returns a proposal for the instantiation of <code>var</code> 
     * iff <code>app</code> is a TacletApp for a loop invariant taclet
     * and <code>var</code> is the SchemaVariable representing the invariant 
     * and the loop on which the taclet matches contains a loop invariant
     * annotation. Otherwise null is returned.
     */
    public String getProposal(TacletApp app, 
    			      SchemaVariable var, 
			      Services services, 
			      Node undoAnchor,
			      ListOfString previousProposals){
	
        final Object inst = tryToInstantiate(app, var, services);
	final LogicPrinter lp = new LogicPrinter(new ProgramPrinter(null), 
						 NotationInfo.createInstance(),
						 services);
	String proposal;        
	try {
	    if (inst instanceof Term){
		lp.printTerm((Term) inst);
		proposal = lp.toString();
	    }  else if (inst instanceof ListOfTerm){
		lp.printTerm((ListOfTerm) inst);
		proposal = lp.toString();
            } else if (inst instanceof SetOfLocationDescriptor) {
                lp.printLocationDescriptors((SetOfLocationDescriptor) inst);
                proposal = lp.toString();
            } else if (var.name().toString().equals("#modifies")) {
		lp.printLocationDescriptors(
                        SetAsListOfLocationDescriptor.EMPTY_SET
                        .add(EverythingLocationDescriptor.INSTANCE));
                proposal = lp.toString();
	    } else { 
		proposal = null;
	    }
	} catch (IOException e){
	    proposal = null;
	}
        
	return proposal;
    }

    /**
     * returns true if the rulesets contain the rule set loop invariant   
     */
    public static boolean inLoopInvariantRuleSet(IteratorOfRuleSet ruleSets) {    
        while (ruleSets.hasNext()) {
            if (ruleSets.next().name().toString().equals("loop_invariant_proposal")) {
                return true;
            }
        }
        return false;
    }
    
    
    private static Term getSelfTerm(Term term, Services services) {
        final Services serv = services;
        
	//ignore updates
	while(term.op() instanceof IUpdateOperator) {
	    term = term.sub(((IUpdateOperator)term.op()).targetPos());
	}
	
	//the remaining term should contain a program 
	//(because this method is only called for apps of taclets 
	//in "loop_invariant_proposal")
	final ProgramElement pe = term.javaBlock().program();
		
	//fetch "self" from innermost non-static method-frame
	Term result = new JavaASTVisitor(pe) {
	    private Term result;
	    protected void doAction(ProgramElement node) {
		node.visit(this);
	    }
	    protected void doDefaultAction(SourceElement node) {
		if(node instanceof MethodFrame && result == null) {
		    MethodFrame mf = (MethodFrame) node;
		    ExecutionContext ec 
		    	= (ExecutionContext) mf.getExecutionContext();
		    ReferencePrefix rp = ec.getRuntimeInstance();
                    if(!(rp instanceof TypeReference) && rp !=null) {
                        result = serv.getTypeConverter().convertToLogicElement(rp);
                    }
		}
	    }
	    public Term run() {
		walk(pe);
		return result;
	    }
	}.run();
		
	return result;
    }
    
    
    /**
     * Returns an instantiation of <code>var</code> 
     * iff <code>app</code> is a TacletApp for a loop invariant taclet
     * and <code>var</code> is the SchemaVariable representing the invariant 
     * and the loop on which the taclet matches contains a loop invariant
     * annotation. Otherwise null is returned.
     * Depending if the var looked for is a list schemavariable or a normal sv
     * a list of terms or a term is returned
     */
    public Object tryToInstantiate(TacletApp app, SchemaVariable var, Services services){	
        Object inst = null;
        if (app instanceof PosTacletApp && 
	    inLoopInvariantRuleSet(app.taclet().ruleSets())) {
	    final PosInOccurrence pos = ((PosTacletApp) app).posInOccurrence();
	    final LoopInvariantAnnotation firstLoopInvAnnot = 
                getFirstLoopInvariantAnnotation(pos.subTerm());
	    if(firstLoopInvAnnot == null) {
		return null;
	    }

	    //prepare replacing the loop invariant's "self"-variable 
	    //by the current "self" term
	    final Term selfTerm = getSelfTerm(pos.subTerm(), services);
	    Map map = new HashMap();
	    map.put(TermBuilder.DF.var(firstLoopInvAnnot.getSelfVar()), 
                    selfTerm);
	    OpReplacer or = new OpReplacer(map);
	    
	    //determine instantiation
            final String varName = var.name().toString();
            if (varName.equals("inv") 
        	    && firstLoopInvAnnot.invariant() != null) {
		inst = or.replace(firstLoopInvAnnot.invariant());
	    } else if(varName.equals("#modifies")
		    && firstLoopInvAnnot.assignable() != null) {
		inst = or.replace(firstLoopInvAnnot.assignable());
	    } else if(var.name().toString().equals("post")
		    && firstLoopInvAnnot.post() != null) {
		inst = or.replace(firstLoopInvAnnot.post());
	    } else if(varName.equals("variant")
		    && firstLoopInvAnnot.variant() != null) {
		inst = or.replace(firstLoopInvAnnot.variant());
	    } else if(varName.equals("#old")) {
		inst = convertToListOfTerm(firstLoopInvAnnot.olds());
	    }
	}
        
	return inst;
    }


    private LoopInvariantAnnotation getFirstLoopInvariantAnnotation(Term t) {
        final Annotation[] a = getFirstLoopStatement(t).getAnnotations();
        
        for(int i = 0; i<a.length; i++){
            if(a[i] instanceof LoopInvariantAnnotation){
                return (LoopInvariantAnnotation) a[i];
            }
        }
        return null;        
    }
    
    private ListOfTerm convertToListOfTerm(ArrayOfTerm array){
	ListOfTerm result =  SLListOfTerm.EMPTY_LIST;
	for (int i = array.size() - 1; i>=0; i--) {
	    result = result.prepend(array.getTerm(i));    	
	}
	return result;
    }

    private LoopStatement getFirstLoopStatement(Term t){
	while(t.op() instanceof IUpdateOperator){
	    t = ( (IUpdateOperator)t.op () ).target ( t );
	}
	return getLoopHelp(t.javaBlock().program());
    }

    private LoopStatement getLoopHelp(ProgramElement pe){
	if(pe instanceof LoopStatement){
	    return (LoopStatement) pe;
	}
	if(pe instanceof StatementContainer){
	    return getLoopHelp(((StatementContainer) pe).getStatementAt(0));
	}
	//shouldn't happen.
	return null;
    }
}
