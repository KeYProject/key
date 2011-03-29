// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;

public class BuiltInRuleAppIndex {

    private BuiltInRuleIndex index;

    private NewRuleListener  newRuleListener =
        NullNewRuleListener.INSTANCE;
    
    public BuiltInRuleAppIndex(BuiltInRuleIndex index) {
	this.index = index;
    }
    
    
    public BuiltInRuleAppIndex(BuiltInRuleIndex index,
			       NewRuleListener  p_newRuleListener) {
	this.index           = index;
	this.newRuleListener = p_newRuleListener;
    }
    
    
    /** 
     * returns a list of built-in rules application applicable
     * for the given goal and position
     */
    public ImmutableList<RuleApp> getBuiltInRule(Goal            goal, 
						 PosInOccurrence pos) {

	ImmutableList<RuleApp> result = ImmutableSLList.<RuleApp>nil();

        for (BuiltInRule builtInRule : index.rules()) {
            BuiltInRule bir = builtInRule;
            if (bir.isApplicable(goal, pos)) {
                RuleApp app = new BuiltInRuleApp(bir, pos);
                result = result.prepend(app);
            }
        }
	return result;
    }


    /** 
     * returns a copy of this index
     */
    public BuiltInRuleAppIndex copy() {
	return new BuiltInRuleAppIndex(index.copy());
    }

    public void setNewRuleListener ( NewRuleListener p_newRuleListener ) {
    	newRuleListener = p_newRuleListener;
    }

    public BuiltInRuleIndex builtInRuleIndex() {
	return index;
    }

    private NewRuleListener getNewRulePropagator () {
    	return newRuleListener;
    }

    public void scanApplicableRules (Goal       goal) {
	scanSimplificationRule ( goal, getNewRulePropagator () );
    }

    private void scanSimplificationRule ( Goal       goal,
					  NewRuleListener listener ) {
        for (BuiltInRule builtInRule : index.rules()) {
            final BuiltInRule bir = builtInRule;
            
            if(bir.isApplicable(goal, null)) {
                BuiltInRuleApp app = new BuiltInRuleApp(bir, null );                            
                listener.ruleAdded ( app, null );
            }
            
            
            scanSimplificationRule(bir, goal, false, listener);
            scanSimplificationRule(bir, goal, true, listener);
        }
    }

  

    private void scanSimplificationRule ( BuiltInRule rule,
					  Goal        goal,
					  boolean     antec,
					  NewRuleListener listener ) {
	final Node                   node = goal.node ();
	final Sequent                seq  = node.sequent ();

        for (Object o : (antec ? seq.antecedent() : seq.succedent())) {
            final ConstrainedFormula cfma = (ConstrainedFormula) o;
            scanSimplificationRule(rule, goal, antec, cfma, listener);
        }
    }


    private void scanSimplificationRule ( BuiltInRule rule, 
                                          Goal goal, 
                                          boolean antec, 
                                          ConstrainedFormula cfma, 
                                          NewRuleListener listener ) {
        final PosInOccurrence    pos = new PosInOccurrence 
		( cfma, PosInTerm.TOP_LEVEL, antec );
        if(rule instanceof UseDependencyContractRule) {//HACK
            scanSimplificationRule(rule, goal, pos, listener);
        } else if (rule.isApplicable ( goal, pos ) ) {
            BuiltInRuleApp app = new BuiltInRuleApp(rule, pos );                            
            listener.ruleAdded ( app, pos );
        }
    }
    
    //TODO: optimise?
    private void scanSimplificationRule ( BuiltInRule rule,
	    				  Goal goal,
                                          PosInOccurrence pos,
                                          NewRuleListener listener ) {
        if (rule.isApplicable ( goal, pos ) ) {
            BuiltInRuleApp app = new BuiltInRuleApp(rule, pos );                            
            listener.ruleAdded ( app, pos );
        }
        for(int i = 0, n = pos.subTerm().arity(); i < n; i++) {
            scanSimplificationRule(rule, goal, pos.down(i), listener);
        }
    }     

    public void reportRuleApps ( NewRuleListener l,
                                 Goal goal ) {
        scanSimplificationRule( goal, l );
    }
    
    /** 
     * called if a formula has been replaced
     * @param sci SequentChangeInfo describing the change of the sequent 
     */  
    public void sequentChanged ( Goal goal, SequentChangeInfo sci ) {        
        scanAddedFormulas ( goal, true, sci );
        scanAddedFormulas ( goal, false, sci );
        
        scanModifiedFormulas ( goal, true, sci );
        scanModifiedFormulas ( goal, false, sci );
    }
    
    private void scanAddedFormulas ( Goal goal, boolean antec, SequentChangeInfo sci ) {
        ImmutableList<ConstrainedFormula> cfmas = sci.addedFormulas( antec );
        final NewRuleListener listener = getNewRulePropagator();
        while ( !cfmas.isEmpty() ) {
            final ConstrainedFormula cfma = cfmas.head();
            for (BuiltInRule builtInRule : index.rules()) {
                final BuiltInRule rule = builtInRule;
                scanSimplificationRule(rule, goal, antec,
                        cfma, listener);
            }
            cfmas = cfmas.tail();
        }
    }


    private void scanModifiedFormulas ( Goal goal, boolean antec, SequentChangeInfo sci ) {
        
        final NewRuleListener listener = getNewRulePropagator();
        ImmutableList<FormulaChangeInfo> fcis = sci.modifiedFormulas( antec );

        while ( !fcis.isEmpty() ) {
            final FormulaChangeInfo fci = fcis.head();               
            final ConstrainedFormula cfma = fci.getNewFormula();
            for (BuiltInRule builtInRule : index.rules()) {
                final BuiltInRule rule = builtInRule;
                scanSimplificationRule(rule, goal, antec, cfma, listener);
            }
            fcis = fcis.tail();
        }
    }
}
