// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Instances of this class are immutable
 */
public class BuiltInRuleAppContainer extends RuleAppContainer {

    BuiltInRuleAppContainer(RuleApp p_app, RuleAppCost p_cost) {
        super(p_app, p_cost);
    }

    /**
     * Create a list of new RuleAppContainers that are to be 
     * considered for application.
     */
    public ImmutableList<RuleAppContainer> createFurtherApps(
        Goal p_goal,
        Strategy p_strategy) {
        if (isStillApplicable(p_goal))
            return createAppContainers(
                (BuiltInRuleApp) getRuleApp(),
                null,
                p_goal,
                p_strategy);
        return ImmutableSLList.<RuleAppContainer>nil();
    }

    /**
     * Create a <code>RuleApp</code> that is suitable to be applied 
     * or <code>null</code>.
     */
    public RuleApp completeRuleApp(Goal p_goal, Strategy p_strategy) {
        if (!isStillApplicable(p_goal))
            return null;

        final BuiltInRuleApp app = getBuiltInRuleApp();
        final BuiltInRule rule = (BuiltInRule) app.rule();
        final Constraint userConstraint = app.userConstraint();
        final PosInOccurrence pio = getBuiltInRuleApp().posInOccurrence();
	
        return new BuiltInRuleApp(rule, pio, userConstraint);
    }

    /**
     * @return the BuiltInRuleApp belonging to this container
     */
    protected BuiltInRuleApp getBuiltInRuleApp() {
        return (BuiltInRuleApp) getRuleApp();
    }

    /**
     * @return true iff the stored rule app is applicable for the given sequent,
     * i.e. if the bound position does still exist (if-formulas are not
     * considered)
     */
    protected boolean isStillApplicable(Goal p_goal) {
        final BuiltInRuleApp app = getBuiltInRuleApp();
	final PosInOccurrence pio = app.posInOccurrence();
	if(pio == null){
	    return app.rule().isApplicable(p_goal, null, app.userConstraint());
	} else {
            final ConstrainedFormula cfma = pio.constrainedFormula();
            final boolean antec = pio.isInAntec();
            final Sequent seq = p_goal.sequent();
            final Semisequent semiseq = antec ? seq.antecedent() : seq.succedent();
            
            return semiseq.contains(cfma);
	}
    }

    /**
     * Create containers for RuleApps.
     * @return list of containers for currently applicable BuiltInRuleApps,
     * the cost may be an instance of <code>TopRuleAppCost</code>.
     */
    static ImmutableList<RuleAppContainer> createAppContainers
        ( BuiltInRuleApp p_app,
          PosInOccurrence p_pio,
          Goal p_goal,
          Strategy p_strategy ) {
        ImmutableList<RuleAppContainer> result = ImmutableSLList.<RuleAppContainer>nil();

        final RuleAppCost cost = p_strategy.computeCost(p_app, p_pio, p_goal);

        BuiltInRuleAppContainer container =
            new BuiltInRuleAppContainer(p_app, cost);

        result = result.prepend(container);

        return result;
    }

}
