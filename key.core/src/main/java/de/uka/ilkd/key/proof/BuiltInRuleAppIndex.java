// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.FormulaChangeInfo;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

public class BuiltInRuleAppIndex {

    private final BuiltInRuleIndex index;

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
    public ImmutableList<IBuiltInRuleApp> getBuiltInRule(Goal            goal, 
						         PosInOccurrence pos) {

	ImmutableList<IBuiltInRuleApp> result = ImmutableSLList.<IBuiltInRuleApp>nil();

        ImmutableList<BuiltInRule> rules = index.rules();
        while (!rules.isEmpty()) {
            final BuiltInRule bir = rules.head();
            rules = rules.tail();
            if (bir.isApplicable(goal, pos)) {
                IBuiltInRuleApp app = bir.createApp(pos, goal.proof().getServices());
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
        ImmutableList<BuiltInRule> rules = index.rules();
        if (!rules.isEmpty()) {
            do {
                final BuiltInRule builtInRule = rules.head();
                rules = rules.tail();
                if(builtInRule.isApplicable(goal, null)) {
                    IBuiltInRuleApp app = builtInRule.createApp( null, goal.proof().getServices() );                            
                    listener.ruleAdded ( app, null );
                }
            } while (!rules.isEmpty());
            scanSimplificationRule(index.rules(), goal, false, listener);
            scanSimplificationRule(index.rules(), goal, true, listener);
        }
    }

  

    private void scanSimplificationRule ( ImmutableList<BuiltInRule> rules,
					  Goal        goal,
					  boolean     antec,
					  NewRuleListener listener ) {
	final Node                   node = goal.node ();
	final Sequent                seq  = node.sequent ();

        for (final SequentFormula sf : (antec ? seq.antecedent() : seq.succedent())) {
            scanSimplificationRule(rules, goal, antec, sf, listener);
        }
    }

    private void scanSimplificationRule ( ImmutableList<BuiltInRule> rules, 
                                          Goal goal, 
                                          boolean antec, 
                                          SequentFormula cfma, 
                                          NewRuleListener listener ) {
        final PosInOccurrence pos = new PosInOccurrence( cfma, PosInTerm.getTopLevel(), antec );
        ImmutableList<BuiltInRule> subrules = ImmutableSLList.nil();
        while (!rules.isEmpty()) {
            final BuiltInRule rule = rules.head();
            rules = rules.tail();
            if(rule.isApplicableOnSubTerms()) {
                subrules = subrules.prepend(rule);
            } else if (rule.isApplicable ( goal, pos ) ) {
                final IBuiltInRuleApp app = rule.createApp( pos, goal.proof().getServices() );
                listener.ruleAdded ( app, pos );                
            }
        }
        scanSimplificationRule(subrules, goal, pos, listener);
    }
    
    //TODO: optimise?
    private void scanSimplificationRule ( ImmutableList<BuiltInRule> rules,
	    				  Goal goal,
                                          PosInOccurrence pos,
                                          NewRuleListener listener ) {
        ImmutableList<BuiltInRule> it = rules;
        while (!it.isEmpty()) {
            final BuiltInRule rule = it.head();
            it = it.tail();
            if (rule.isApplicable ( goal, pos ) ) {
                IBuiltInRuleApp app = rule.createApp( pos, goal.proof().getServices() );                            
                listener.ruleAdded ( app, pos );
            }
        }
        for(int i = 0, n = pos.subTerm().arity(); i < n; i++) {
            scanSimplificationRule(rules, goal, pos.down(i), listener);
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
        ImmutableList<SequentFormula> cfmas = sci.addedFormulas( antec );
        final NewRuleListener listener = getNewRulePropagator();
        while ( !cfmas.isEmpty() ) {
            final SequentFormula cfma = cfmas.head();
                scanSimplificationRule(index.rules(), goal, antec, cfma, listener);
            cfmas = cfmas.tail();
        }
    }


    private void scanModifiedFormulas ( Goal goal, boolean antec, SequentChangeInfo sci ) {
        
        final NewRuleListener listener = getNewRulePropagator();
        ImmutableList<FormulaChangeInfo> fcis = sci.modifiedFormulas( antec );

        while ( !fcis.isEmpty() ) {
            final FormulaChangeInfo fci = fcis.head();               
            final SequentFormula cfma = fci.getNewFormula();            
            scanSimplificationRule(index.rules(), goal, antec, cfma, listener);
            fcis = fcis.tail();
        }
    }
}
