//This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.explicitheap;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.CreatingASTVisitor;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.ExtList;


/**
 * Collection of some common, stateless functionality. Stolen from
 * the weissInvariants side branch.
 */
class InvInferenceTools {
    
    public static final InvInferenceTools INSTANCE = new InvInferenceTools();
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    
    private InvInferenceTools() {}
    
    
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
     * Universally closes a formula.
     */
    public Term close(Term formula) {
	assert formula.sort() == Sort.FORMULA;
	return TB.all(formula.freeVars().toArray(), formula);
    }
    
    
    /**
     * Returns the set of elementary conjuncts of the passed formula.
     */
    public SetOfTerm toSet(Term formula) {
	SetOfTerm result = SetAsListOfTerm.EMPTY_SET;
        ListOfTerm workingList = SLListOfTerm.EMPTY_LIST.prepend(formula);
        while(!workingList.isEmpty()) {
            Term f = workingList.head();
            workingList = workingList.tail();
            if(f.op() == Junctor.AND) {
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
    public Term toFormula(SetOfTerm set) {
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
     * Returns the innermost method frame of the java block of the passed term.
     * @param term A term of the form "{u}[p]psi"
     * @param services The services object. 
     */
    public MethodFrame getInnermostMethodFrame(Term term, Services services) {
        //ignore updates
        while(term.op() instanceof IUpdateOperator) {
            term = term.sub(((IUpdateOperator)term.op()).targetPos());
        }
        
        //the remaining term should have a Java block 
        final ProgramElement pe = term.javaBlock().program();
                
        //fetch "self" from innermost method-frame
        MethodFrame result = new JavaASTVisitor(pe, services) {
            private MethodFrame result;
            protected void doAction(ProgramElement node) {
                node.visit(this);
            }
            protected void doDefaultAction(SourceElement node) {
                if(node instanceof MethodFrame) {
                    result = (MethodFrame) node;
                }
            }
            public MethodFrame run() {
                walk(pe);
                return result;
            }
        }.run();
                
        return result;
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
        while(term.op() instanceof IUpdateOperator) {
            term = term.sub(((IUpdateOperator)term.op()).targetPos());
        }        
        return term;
    }
    
    
    /**
     * Returns the entry node for the innermost loop of the symbolic 
     * execution state given by the passed node.
     */
    public Node getEntryNodeForInnermostLoop(Node node) {
        ListOfLoopStatement leftLoops 
            = SLListOfLoopStatement.EMPTY_LIST;
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
    public boolean areDisjoint(SetOfUpdateableOperator set1, SetOfUpdateableOperator set2) {
	for(UpdateableOperator loc : set1) {
            if(set2.contains(loc)) {
                return false;
            }
        }
        return true;
    }
    
    
    /**
     * Collects all location symbols occurring in the passed term.
     */
    public SetOfUpdateableOperator getOccurringLocationSymbols(Term t) {
        SetOfUpdateableOperator result = SetAsListOfUpdateableOperator.EMPTY_SET;
        if(t.op() instanceof UpdateableOperator) {
            result = result.add((UpdateableOperator)t.op());
        }
        if(t.javaBlock() != null && t.javaBlock().program() != null) {
            JavaASTCollector jac = new JavaASTCollector(t.javaBlock().program(), 
                                                        UpdateableOperator.class);
            jac.start();
            for(ProgramElement loc : jac.getNodes()) {
                result = result.add((UpdateableOperator)loc);
            }
        }
        for(int i = 0; i < t.arity(); i++) {
            result = result.union(getOccurringLocationSymbols(t.sub(i)));
        }
        return result;
    }
}
