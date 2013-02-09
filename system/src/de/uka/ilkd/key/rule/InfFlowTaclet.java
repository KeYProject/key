/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableMap;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.StrategyInfoUndoMethod;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.util.properties.Properties;


/**
 *
 * @author christoph
 */
public class InfFlowTaclet extends RewriteTaclet {

    public static final Properties.Property<ImmutableList<Term>> INF_FLOW_CONTRACT_APPL_PROPERTY =
            new Properties.Property<ImmutableList<Term>>(
                    (Class<ImmutableList<Term>>) (Class<?>) ImmutableList.class,
                     "information flow contract " +
                             "applicaton property");


    public InfFlowTaclet(Name name,
                         TacletApplPart applPart,
                         ImmutableList<TacletGoalTemplate> goalTemplates,
                         ImmutableList<RuleSet> ruleSets,
                         TacletAttributes attrs,
                         Term find,
                         ImmutableMap<SchemaVariable, TacletPrefix> prefixMap,
                         int p_applicationRestriction,
                         ImmutableSet<Choice> choices) {
        super(name, applPart, goalTemplates, ruleSets, attrs, find, prefixMap, p_applicationRestriction, choices);
    }


    public InfFlowTaclet(Name name,
                         TacletApplPart applPart,
                         ImmutableList<TacletGoalTemplate> goalTemplates,
                         ImmutableList<RuleSet> ruleSets,
                         TacletAttributes attrs,
                         Term find,
                         ImmutableMap<SchemaVariable, TacletPrefix> prefixMap,
                         int p_applicationRestriction,
                         ImmutableSet<Choice> choices,
                         boolean surviveSymbExec) {
        super(name, applPart, goalTemplates, ruleSets, attrs, find, prefixMap, p_applicationRestriction, choices, surviveSymbExec);
    }


    @Override
    protected void addToAntec(Semisequent semi,
                              Goal goal,
                              PosInOccurrence pos,
                              Services services,
                              MatchConditions matchCond) {
        final ImmutableList<SequentFormula> replacements =
            instantiateSemisequent(semi, services, matchCond);
        assert replacements.size() == 1 : "information flow taclets must have " +
                                  "exactly one add!";
        updateStrategyInfo(goal, replacements.iterator().next().formula());
        super.addToAntec(semi, goal, pos, services, matchCond);
    }


    public void updateStrategyInfo(Goal goal,
                                   final Term applFormula) {
        ImmutableList<Term> applFormulas =
                goal.getStrategyInfo(INF_FLOW_CONTRACT_APPL_PROPERTY);
        if (applFormulas == null) {
            applFormulas = ImmutableSLList.<Term>nil();
        }
        applFormulas = applFormulas.append(applFormula);
        StrategyInfoUndoMethod undo = new StrategyInfoUndoMethod() {

            @Override
            public void undo(Properties strategyInfos) {
                ImmutableList<Term> applFormulas =
                        strategyInfos.get(INF_FLOW_CONTRACT_APPL_PROPERTY);
                strategyInfos.put(INF_FLOW_CONTRACT_APPL_PROPERTY, applFormulas.removeAll(applFormula));
            }
        };
        goal.addStrategyInfo(INF_FLOW_CONTRACT_APPL_PROPERTY, applFormulas, undo);

    }
}
