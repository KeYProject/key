//This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.util;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.*;


/**
 * Collection of some common, stateless functionality. Stolen from
 * the weissInvariants side branch.
 */
public class InvInferenceTools {
    
    public static final InvInferenceTools INSTANCE = new InvInferenceTools();
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    private InvInferenceTools() {}
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    /**
     * Removes universal quantifiers from a formula.
     */
    public Term open(Term formula) {
	assert formula.sort() == Sort.FORMULA;
	if(formula.op() == Quantifier.ALL) {
	    return open(formula.sub(0)); 
	} else {
	    return formula;
	}
    }
    
    
    /**
     * Returns the set of elementary conjuncts of the passed formula.
     */
    public ImmutableSet<Term> toSet(Term formula) {
	assert formula.sort().equals(Sort.FORMULA);
	ImmutableSet<Term> result = DefaultImmutableSet.<Term>nil();
        ImmutableList<Term> workingList 
        	= ImmutableSLList.<Term>nil().prepend(formula);
        while(!workingList.isEmpty()) {
            final Term f = workingList.head();
            workingList = workingList.tail();
            if(f.op() == Junctor.AND) {
                workingList = workingList.prepend(f.sub(1)).prepend(f.sub(0));
            } else {
                result = result.add(f);
            }
        }
        return result;
    }
    
    
    public ImmutableSet<Term> unionToSet(Term s, Services services) {
	final LocSetLDT setLDT = services.getTypeConverter().getLocSetLDT();
	assert s.sort().equals(setLDT.targetSort());
	final Function union = setLDT.getUnion();
	ImmutableSet<Term> result = DefaultImmutableSet.<Term>nil();
        ImmutableList<Term> workingList = ImmutableSLList.<Term>nil().prepend(s);
        while(!workingList.isEmpty()) {
            Term f = workingList.head();
            workingList = workingList.tail();
            if(f.op() == union) {
                workingList = workingList.prepend(f.sub(1)).prepend(f.sub(0));
            } else {
                result = result.add(f);
            }
        }
        return result;
    }
    

    /**
     * Conjoins the formulas in the passed set.
     */
    public Term toFormula(ImmutableSet<Term> set) {
	Term result = TB.tt();
	for(Term term : set) {
	    result = TB.and(result, term);
	}
	return result;
    }

    
    /**
     * Returns the active statement of the passed a java block.
     */
    public SourceElement getActiveStatement(JavaBlock jb) {
	assert jb.program() != null;
	
        SourceElement result = jb.program().getFirstElement();
        while(result instanceof ProgramPrefix
              && !(result instanceof StatementBlock 
                   && ((StatementBlock)result).isEmpty())) {
            if(result instanceof LabeledStatement) {
                result = ((LabeledStatement)result).getChildAt(1);
            } else {
                result = result.getFirstElement();
            }
        }
        return result;
    }
    
    
    /**
     * Returns the passed java block without its active statement.
     */
    public JavaBlock removeActiveStatement(JavaBlock jb, Services services) {
        assert jb.program() != null;
        final SourceElement activeStatement = getActiveStatement(jb);
        Statement newProg = (Statement)
            (new CreatingASTVisitor(jb.program(), false, services) {
                private boolean done = false;
                
                public ProgramElement go() {
                    stack.push(new ExtList());
                    walk(root());
                    ExtList el = stack.peek();
                    return (ProgramElement) el.get(ProgramElement.class); 
                }
                
                public void doAction(ProgramElement node) {
                    if(!done && node == activeStatement) {
                        done = true;
                        stack.pop();                    
                        changed();
                    } else {
                        super.doAction(node);
                    }
                }
            }).go();
        
        StatementBlock newSB = newProg instanceof StatementBlock 
                               ? (StatementBlock)newProg
                               : new StatementBlock(newProg);              
        return JavaBlock.createJavaBlock(newSB);
    }
    
    
    /**
     * Returns the innermost method frame of the passed java block
     */
    public MethodFrame getInnermostMethodFrame(JavaBlock jb, 
	    				       Services services) { 
        final ProgramElement pe = jb.program();
        final MethodFrame result = new JavaASTVisitor(pe, services) {
            private MethodFrame res;
            protected void doAction(ProgramElement node) {
                node.visit(this);
            }
            protected void doDefaultAction(SourceElement node) {
                if(node instanceof MethodFrame && res == null) {
                    res = (MethodFrame) node;
                }
            }
            public MethodFrame run() {
                walk(pe);
                return res;
            }
        }.run();
                
        return result;
    }
    
    
    public ExecutionContext getInnermostExecutionContext(JavaBlock jb, 
	    						 Services services) {
	final MethodFrame frame = getInnermostMethodFrame(jb, services);
	return frame == null 
               ? null
	       : (ExecutionContext) frame.getExecutionContext();	
    }
    
    
    /**
     * Returns the receiver term of the passed method frame, or null if
     * the frame belongs to a static method.
     */
    public Term getSelfTerm(MethodFrame mf, Services services) {
	ExecutionContext ec = (ExecutionContext) mf.getExecutionContext();
	ReferencePrefix rp = ec.getRuntimeInstance();
	if(!(rp instanceof TypeReference) && rp != null) {
	    return services.getTypeConverter().convertToLogicElement(rp);
	} else {
	    return null;
	}
    }
    
    
    /**
     * Removes all formulas from the passed goal.
     */
    public void clearGoal(Goal goal) {
	for(ConstrainedFormula cf : goal.sequent().antecedent()) {
            PosInOccurrence pio = new PosInOccurrence(cf, 
                                                      PosInTerm.TOP_LEVEL, 
                                                      true);
            goal.removeFormula(pio);
        }
	for(ConstrainedFormula cf : goal.sequent().succedent()) {
            PosInOccurrence pio = new PosInOccurrence(cf, 
                                                      PosInTerm.TOP_LEVEL, 
                                                      false);
            goal.removeFormula(pio);
        }
    }
    
    
    /**
     * Tells whether the passed rule belongs to the specified rule set. 
     */
    public boolean belongsTo(Rule rule, String ruleSetName) {	
        if(rule instanceof Taclet) {
    	    if(ruleSetName.endsWith("*")) {
    		ruleSetName 
    			= ruleSetName.substring(0, ruleSetName.length() - 1);
                for(RuleSet rs : ((Taclet)rule).getRuleSets()) {
                    if(rs.toString().startsWith(ruleSetName)) {
                        return true;
                    }
                }    	    
    	    } else {
                for(RuleSet rs : ((Taclet)rule).getRuleSets()) {
                    if(rs.toString().equals(ruleSetName)) {
                        return true;
                    }
                }
    	    }
        }
        return false;
    }
    

    /**
     * Tells whether the passed rule belongs to one of the specified rule sets.
     */
    public boolean belongsTo(Rule rule, String[] ruleSetNames) {
        for(int i = 0; i < ruleSetNames.length; i++) {
            if(belongsTo(rule, ruleSetNames[i])) {
                return true;
            }
        }
        return false;
    }
    
    
    /**
     * Tells whether the passed rule is one of those specified by the second
     * argument.
     */
    public boolean isOneOf(Rule rule, String[] ruleNames) {
	String s = rule.name().toString();
	for(int i = 0; i < ruleNames.length; i++) {
	    if(s.equals(ruleNames[i])) {
		return true;
	    }
	}
	return false;
    }
    
    
    /**
     * Removes leading updates from the passed term.
     */
    public Term goBelowUpdates(Term term) {
        while(term.op() instanceof UpdateApplication) {
            term = UpdateApplication.getTarget(term);
        }        
        return term;
    }
    
    
    /**
     * Removes leading updates from the passed term.
     */
    public Pair<ImmutableList<Term>,Term> goBelowUpdates2(Term term) {
	ImmutableList<Term> updates = ImmutableSLList.<Term>nil();
        while(term.op() instanceof UpdateApplication) {
            updates = updates.append(UpdateApplication.getUpdate(term));
            term = UpdateApplication.getTarget(term);
        }        
        return new Pair<ImmutableList<Term>,Term>(updates, term);
    }    
    
    
    /**
     * Returns the entry node for the innermost loop of the symbolic 
     * execution state given by the passed node.
     */
    public Node getEntryNodeForInnermostLoop(Node node) {
        ImmutableList<LoopStatement> leftLoops 
            = ImmutableSLList.<LoopStatement>nil();
        for(Node n = node.parent(); n != null; n = n.parent()) {
            RuleApp app = n.getAppliedRuleApp();
            Rule rule = app.rule();
            if(belongsTo(rule, "loop_expand")) {
                Term progTerm 
                    = goBelowUpdates(app.posInOccurrence().subTerm());
                LoopStatement loop 
                    = (LoopStatement) getActiveStatement(progTerm.javaBlock());
                
                //left?
                boolean alreadyLeft = false;
                for(LoopStatement leftLoop : leftLoops) {
                    if(leftLoop.equalsModRenaming(loop, 
                                                  new NameAbstractionTable())) {
                        alreadyLeft = true;
                        break;
                    }
                }
                if(!alreadyLeft) {
                    return n;
                }
            } else if(rule == WhileInvariantRule.INSTANCE) {
                Term progTerm 
                    = goBelowUpdates(app.posInOccurrence().subTerm());
                LoopStatement loop 
                    = (LoopStatement) getActiveStatement(progTerm.javaBlock());
                leftLoops = leftLoops.prepend(loop);
            }
        }
        return null;
    }
    
    
    /**
     * Returns the entry node for the passed loop and the symbolic execution
     * state given by the passed node.
     */
    public Node getEntryNodeForLoop(Node node, LoopStatement loop) {
        for(Node n = node.parent(); n != null; n = n.parent()) {            
            RuleApp app = n.getAppliedRuleApp();
            Rule rule = app.rule();
            if(belongsTo(rule, "loop_expand")) {
                Term progTerm 
                    = goBelowUpdates(app.posInOccurrence().subTerm());
                LoopStatement l 
                    = (LoopStatement) getActiveStatement(progTerm.javaBlock());
                if(loop.equalsModRenaming(l, new NameAbstractionTable())) {
                    return n;
                }
            } else if(rule == WhileInvariantRule.INSTANCE) {
                Term progTerm 
                    = goBelowUpdates(app.posInOccurrence().subTerm());
                LoopStatement l 
                    = (LoopStatement) getActiveStatement(progTerm.javaBlock());
                if(loop.equalsModRenaming(l, new NameAbstractionTable())) {
                    return null;
                }                
            }
        }
        return null;
    }
    
    
    /**
     * Tells whether the passed sets of location symbols are disjoint.
     */
    public boolean areDisjoint(ImmutableSet<UpdateableOperator> set1, ImmutableSet<UpdateableOperator> set2) {
	for(UpdateableOperator loc : set1) {
            if(set2.contains(loc)) {
                return false;
            }
        }
        return true;
    }
    
    
    public ImmutableSet<ProgramVariable> getLocalIns(ProgramElement pe, 
	    					     Services services) {
	final ReadPVCollector rpvc = new ReadPVCollector(pe, services);
	rpvc.start();
	return rpvc.result();
    }    
    
    
    public ImmutableSet<ProgramVariable> getLocalOuts(ProgramElement pe, 
	    			                      Services services) {
	final WrittenPVCollector wpvc = new WrittenPVCollector(pe, services);
	wpvc.start();
	return wpvc.result();
    }
    
    
    
    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------    
    
    private static final class ReadPVCollector extends JavaASTVisitor {
	private ImmutableSet<ProgramVariable> result 
		= DefaultImmutableSet.<ProgramVariable>nil();

	private ImmutableSet<ProgramVariable> declaredPVs 
		= DefaultImmutableSet.<ProgramVariable>nil();

	public ReadPVCollector(ProgramElement root, Services services) {
	    super(root, services);
	}

	@Override
	protected void doDefaultAction(SourceElement node) {
	    if(node instanceof ProgramVariable) {
		ProgramVariable pv = (ProgramVariable) node;
		if(!pv.isMember() && !declaredPVs.contains(pv)) {
		    result = result.add(pv);
		}		    
	    } else if(node instanceof VariableSpecification) {
		VariableSpecification vs = (VariableSpecification) node;
		ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
		if(!pv.isMember()) {
		    assert !declaredPVs.contains(pv);
		    result = result.remove(pv);
		    declaredPVs = declaredPVs.add(pv);
		}
	    }
	}

	public ImmutableSet<ProgramVariable> result() {
	    return result;
	}
    }
    
       
    private static final class WrittenPVCollector extends JavaASTVisitor {
	private ImmutableSet<ProgramVariable> result 
		= DefaultImmutableSet.<ProgramVariable>nil();

	private ImmutableSet<ProgramVariable> declaredPVs 
		= DefaultImmutableSet.<ProgramVariable>nil();

	public WrittenPVCollector(ProgramElement root, Services services) {
	    super(root, services);
	}

	@Override	
	protected void doDefaultAction(SourceElement node) {
	    if(node instanceof Assignment) {
		ProgramElement lhs = ((Assignment) node).getChildAt(0);
		if(lhs instanceof ProgramVariable) {
		    ProgramVariable pv = (ProgramVariable) lhs;
		    if(!pv.isMember() && !declaredPVs.contains(pv)) {
			result = result.add(pv);
		    }		    
		}
	    } else if(node instanceof VariableSpecification) {
		VariableSpecification vs = (VariableSpecification) node;
		ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
		if(!pv.isMember()) {
		    assert !declaredPVs.contains(pv);
		    assert !result.contains(pv);
		    declaredPVs = declaredPVs.add(pv);
		}
	    }
	}

	public ImmutableSet<ProgramVariable> result() {
	    return result;
	}
    }
}
