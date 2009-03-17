// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.io.IOException;
import java.util.Map;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.rule.IteratorOfRuleSet;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.speclang.LoopInvariant;


public class LoopInvariantProposer implements InstantiationProposer {

    /**
     * An instance of LoopInvariantProposer
     */
    public static final LoopInvariantProposer DEFAULT = new LoopInvariantProposer();
    
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    private LoopInvariantProposer() {        
    }
    

    
    //-------------------------------------------------------------------------
    //internal methods
    //------------------------------------------------------------------------- 
    
    private LoopStatement getLoopHelp(ProgramElement pe){
        if(pe instanceof LoopStatement){
            return (LoopStatement) pe;
        } else if(pe instanceof StatementContainer){
            return getLoopHelp(((StatementContainer) pe).getStatementAt(0));
        } else {
            assert false;
            return null;
        }
    }
    
    
    private LoopStatement getFirstLoopStatement(Term t){
        while(t.op() instanceof IUpdateOperator){
            t = ( (IUpdateOperator)t.op () ).target ( t );
        }
        return getLoopHelp(t.javaBlock().program());
    }


    private LoopInvariant getLoopInvariant(Term t, Services services) {
        LoopStatement loop = getFirstLoopStatement(t);
        return services.getSpecificationRepository().getLoopInvariant(loop);
    }
    

    
    //-------------------------------------------------------------------------
    //public interface
    //------------------------------------------------------------------------- 

    /**
     * returns true if the rulesets contain the rule set loop invariant   
     */
    public boolean inLoopInvariantRuleSet(Taclet taclet) {
        if(taclet == null) {
            return true;
        }
        IteratorOfRuleSet it = taclet.ruleSets();
        while(it.hasNext()) {
            if(it.next().name().toString().equals("loop_invariant_proposal")) {
                return true;
            }
        }
        return false;
    }
    
    /**
     * Returns the receiver term of the innermost method frame of
     * the java block of the passed term, or null if the innermost
     * frame is that of a static method.
     * @param term A term of the form "{u}[p]psi"
     * @param services The services object. 
     */
    public Term getInnermostSelfTerm(Term term, Services services) {
        //ignore updates
        while(term.op() instanceof IUpdateOperator) {
            term = term.sub(((IUpdateOperator)term.op()).targetPos());
        }
        
        //the remaining term should have a Java block 
        final ProgramElement pe = term.javaBlock().program();
                
        //fetch "self" from innermost method-frame
        Term result = new JavaASTVisitor(pe, services) {
            private Term result;
            private boolean done = false;
            protected void doDefaultAction(SourceElement node) {
                if(node instanceof MethodFrame && !done) {
                    done = true;
                    MethodFrame mf = (MethodFrame) node;
                    ExecutionContext ec 
                        = (ExecutionContext) mf.getExecutionContext();
                    ReferencePrefix rp = ec.getRuntimeInstance();
                    if(!(rp instanceof TypeReference) && rp != null) {
                        result = services.getTypeConverter()
                                         .convertToLogicElement(rp);
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
    public Object tryToInstantiate(TacletApp app, 
                                   SchemaVariable var, 
                                   Services services) {
        Object inst = null;
        if (app instanceof PosTacletApp 
            && inLoopInvariantRuleSet(app.taclet())) {
            final PosInOccurrence pos = ((PosTacletApp) app).posInOccurrence();
            final LoopInvariant inv = getLoopInvariant(pos.subTerm(), services);
            if(inv == null) {
                return null;
            }
            
            //determine instantiation
            final Term selfTerm = getInnermostSelfTerm(pos.subTerm(), services);
            final Map<Operator, Function> atPreFunctions = inv.getInternalAtPreFunctions();
            final String varName = var.name().toString();
            if (varName.equals("inv")) {
                assert var.isFormulaSV();
                inst = inv.getInvariant(selfTerm, atPreFunctions, services);
            } else if(varName.equals("predicates")) {
                assert var.isListSV();
                assert var.matchType() == Term.class;
                inst =inv.getPredicates(selfTerm, atPreFunctions, services);
            } else if(varName.equals("#modifies")) {
                assert var.isListSV();
                assert var.matchType() == LocationDescriptor.class;
                inst = inv.getModifies(selfTerm, atPreFunctions, services);
            } else if(varName.equals("variant")) {
                assert var.isTermSV();
                inst = inv.getVariant(selfTerm, atPreFunctions, services);
            }
        }
        
        return inst;
    }
    
    
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
	
        final Object inst = tryToInstantiate(app, 
                                             var, 
                                             services);
	final LogicPrinter lp = new LogicPrinter(new ProgramPrinter(null), 
						 NotationInfo.createInstance(),
						 services);
                
	String proposal;
	try {
	    if (inst instanceof Term){
		lp.printTerm((Term) inst);
		proposal = lp.toString();
	    }  else if (inst instanceof SetOfTerm){
		lp.printTerm((SetOfTerm) inst);
		proposal = lp.toString();
            } else if (inst instanceof SetOfLocationDescriptor) {
                lp.printLocationDescriptors((SetOfLocationDescriptor) inst);
                proposal = lp.toString();
            } else { 
		proposal = null;
	    }
	} catch (IOException e){
	    proposal = null;
	}
        
	return proposal;
    }
}
