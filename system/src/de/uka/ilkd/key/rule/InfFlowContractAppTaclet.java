/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableMap;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.StrategyInfoUndoMethod;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.util.properties.Properties;


/**
 * A normal RewriteTaclet except that the formula which is added by this taclet
 * is also added to the list of formulas contained in the
 * INF_FLOW_CONTRACT_APPL_PROPERTY. The INF_FLOW_CONTRACT_APPL_PROPERTY is used
 * by the macros UseInformationFlowContractMacro and
 * PrepareInfFlowContractPreBranchesMacro to decide how to prepare the formulas
 * resulting from information flow contract applications.
 * 
 * @author christoph
 */
public class InfFlowContractAppTaclet extends RewriteTaclet {

    public static final String USE_IF = "Use information flow contract for ";
    private static ImmutableSet<Name> alreadyRegistered = DefaultImmutableSet.<Name>nil();

    /**
     * Strategy property which saves the list of formulas which where added
     * by information flow contract applications. This list is used by the
     * macros UseInformationFlowContractMacro and
     * PrepareInfFlowContractPreBranchesMacro to decide how to prepare the
     * formulas resulting from information flow contract applications.
     */
    public static final Properties.Property<ImmutableList<Term>> INF_FLOW_CONTRACT_APPL_PROPERTY =
            new Properties.Property<ImmutableList<Term>>(
                    (Class<ImmutableList<Term>>) (Class<?>) ImmutableList.class,
                     "information flow contract applicaton property");


    public static boolean hasType(Rule rule) {
        return rule != null && rule.name().toString().startsWith(USE_IF);
    }


    public static boolean registered(Name name) {
        return name != null && alreadyRegistered.contains(name);
    }


    public static void register(Name name) {
        alreadyRegistered = alreadyRegistered.add(name);
    }


    public static boolean unregister(Name name) {
        final boolean registered = registered(name);
        if (registered) {
            alreadyRegistered = alreadyRegistered.remove(name);
        }
        return registered;
    }


    public InfFlowContractAppTaclet(Name name,
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


    public InfFlowContractAppTaclet(Name name,
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
                              SequentChangeInfo currentSequent,
                              PosInOccurrence pos,
                              Services services,
                              MatchConditions matchCond,
                              PosInOccurrence applicationPosInOccurrence) {
        final ImmutableList<SequentFormula> replacements =
            instantiateSemisequent(semi, services, matchCond, pos);
        assert replacements.size() == 1 : "information flow taclets must have " +
                                  "exactly one add!";
        updateStrategyInfo(services.getProof().openEnabledGoals().head(),
                           replacements.iterator().next().formula());
        super.addToAntec(semi, currentSequent, pos, services, matchCond, applicationPosInOccurrence);
    }


    /**
     * Add the contract application formula to the list of the
     * INF_FLOW_CONTRACT_APPL_PROPERTY.
     * @param goal          the current goal
     * @param applFormula   the information contract application formula added
     *                      by this taclet
     */
    private void updateStrategyInfo(Goal goal,
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
