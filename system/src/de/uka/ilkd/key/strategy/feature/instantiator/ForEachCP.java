// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.strategy.feature.instantiator;

import java.util.Iterator;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.termProjection.TermBuffer;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;


/**
 * Feature representing a <code>ChoicePoint</code> that iterates over the
 * terms returned by a <code>TermGenerator</code>. The terms are stored in a
 * <code>TermBuffer</code> one after the other and can subsequently be used
 * to instantiate a rule application
 */
public class ForEachCP implements Feature {

    private final BackTrackingManager manager;

    private final TermBuffer var;
    private final TermGenerator generator;
    private final Feature body;
    
    /**
     * @param var
     *            <code>TermBuffer</code> in which the terms are going to
     *            be stored
     * @param generator
     *            the terms that are to be iterated over
     * @param body
     *            a feature that is supposed to be evaluated repeatedly for the
     *            possible values of <code>var</code>
     */
    public static Feature create(TermBuffer var,
                                 TermGenerator generator,
                                 Feature body,
                                 BackTrackingManager manager) {
        return new ForEachCP ( var, generator, body, manager );
    }

    private ForEachCP(TermBuffer var,
                      TermGenerator generator,
                      Feature body,
                      BackTrackingManager manager) {
        this.var = var;
        this.generator = generator;
        this.body = body;
        this.manager = manager;
    }

    public RuleAppCost compute(final RuleApp app,
                               final PosInOccurrence pos,
                               final Goal goal) {
        final Term outerVarContent = var.getContent ();
        var.setContent ( null );
        
        manager.passChoicePoint ( new CP ( app, pos, goal ), this );
       
        final RuleAppCost res;
        if ( var.getContent() != null )
            res = body.compute ( app, pos, goal );
        else
            res = LongRuleAppCost.ZERO_COST;
        
        var.setContent ( outerVarContent );
        return res;
    }

    private final class CP implements ChoicePoint {
        private final class BranchIterator implements Iterator<CPBranch> {
            private final Iterator<Term> terms;
            private final RuleApp        oldApp;

            private BranchIterator(Iterator<Term> terms, RuleApp oldApp) {
                this.terms = terms;
                this.oldApp = oldApp;
            }

            public boolean hasNext() {
                return terms.hasNext ();
            }

            public CPBranch next() {
                final Term generatedTerm = terms.next ();
                return new CPBranch () {
                    public void choose() {
                        var.setContent ( generatedTerm );
                    }
                    public RuleApp getRuleAppForBranch() {
                        return oldApp;
                    }
                };
            }

            public void remove() {
                throw new UnsupportedOperationException();
            }
        }

        private final PosInOccurrence pos;
        private final RuleApp         app;
        private final Goal            goal;
    
        private CP(RuleApp app, PosInOccurrence pos, Goal goal) {
            this.pos = pos;
            this.app = app;
            this.goal = goal;
        }
    
        public Iterator<CPBranch> getBranches(RuleApp oldApp) {
            return new BranchIterator ( generator.generate ( app, pos, goal ),
                                        oldApp );
        }
    }
    
}
