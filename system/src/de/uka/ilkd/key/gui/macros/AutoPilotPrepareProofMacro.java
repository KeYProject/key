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

package de.uka.ilkd.key.gui.macros;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

public class AutoPilotPrepareProofMacro extends StrategyProofMacro {

    private static final String[] ADMITTED_RULES = {
        "orRight", "impRight", "close", "andRight"
    };

    private static final Set<String> ADMITTED_RULES_SET = asSet(ADMITTED_RULES);

    private static final Name NON_HUMAN_INTERACTION_RULESET = new Name("notHumanReadable");

    @Override
    public String getName() {
        return "Auto pilot (preparation only)";
    }

    @Override
    public String getDescription() {
        return "<html><ol><li>Finish symbolic execution" +
                "<li>Separate proof obligations" +
                "<li>Expand invariant definitions</ol>";
    }

    /*
     * convert a string array to a set of strings
     */
    protected static Set<String> asSet(String[] strings) {
        return Collections.unmodifiableSet(new LinkedHashSet<String>(Arrays.asList(strings)));
    }

    /*
     * find a modality term in a node
     */
    private static boolean hasModality(Node node) {
        Sequent sequent = node.sequent();
        for (SequentFormula sequentFormula : sequent) {
            if(hasModality(sequentFormula.formula())) {
                return true;
            }
        }

        return false;
    }

    /*
     * recursively descent into the term to detect a modality.
     */
    private static boolean hasModality(Term term) {
        if(term.op() instanceof Modality) {
            return true;
        }

        for (Term sub : term.subs()) {
            if(hasModality(sub)) {
                return true;
            }
        }

        return false;
    }

    /*
     * Checks if a rule is marked as not suited for interaction.
     */
    private static boolean isNonHumanInteractionTagged(Rule rule) {
        return isInRuleSet(rule, NON_HUMAN_INTERACTION_RULESET);
    }

    private static boolean isInRuleSet(Rule rule, Name ruleSetName) {
        if (rule instanceof Taclet) {
            Taclet taclet = (Taclet) rule;
            for (RuleSet rs : taclet.getRuleSets()) {
                if (ruleSetName.equals(rs.name())) 
                    return true;
            }
        }
        return false;
    }
    
    private static class AutoPilotStrategy implements Strategy {

        private static final Name NAME = new Name("Autopilot filter strategy");
        private final Strategy delegate;

        public AutoPilotStrategy(KeYMediator mediator, PosInOccurrence posInOcc) {
            this.delegate = mediator.getInteractiveProver().getProof().getActiveStrategy();
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            return computeCost(app, pio, goal) != TopRuleAppCost.INSTANCE &&
                   // Assumptions are normally not considered by the cost
                   // computation, because they are normally not yet
                   // instantiated when the costs are computed. Because the
                   // application of a rule sometimes makes sense only if
                   // the assumptions are instantiated in a particular way
                   // (for instance equalities should not be applied on
                   // themselves), we need to give the delegate the possiblity
                   // to reject the application of a rule by calling
                   // isApprovedApp. Otherwise, in particular equalities may
                   // be applied on themselves.
                   delegate.isApprovedApp(app, pio, goal);
        }

        @Override
        public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {

            Rule rule = app.rule();
            if(isNonHumanInteractionTagged(rule)) {
                return TopRuleAppCost.INSTANCE;
            }

            if(hasModality(goal.node())) {
                return delegate.computeCost(app, pio, goal);
            }

            String name = rule.name().toString();
            if(ADMITTED_RULES_SET.contains(name)) {
                return NumberRuleAppCost.getZeroCost();
            }
            
            // apply OSS to <inv>() calls.
            if(rule instanceof OneStepSimplifier) {
                Term target = pio.subTerm();
                if(target.op() instanceof UpdateApplication) {
                    Operator updatedOp = target.sub(1).op();
                    if(updatedOp instanceof ObserverFunction) {
                        return NumberRuleAppCost.getZeroCost();
                    }
                }
            }

            return TopRuleAppCost.INSTANCE;
        }

        @Override
        public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                RuleAppCostCollector collector) {
            delegate.instantiateApp(app, pio, goal, collector);
        }

    }

    @Override
    protected Strategy createStrategy(KeYMediator mediator, PosInOccurrence posInOcc) {
        return new AutoPilotStrategy(mediator, posInOcc);
    }
}
