// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.merge;

import java.util.HashMap;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Triple;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
public class MergePointRule implements BuiltInRule {
    public static final JoinPointRule INSTANCE = new MergePointRule();

    private static final String DISPLAY_NAME = "Join Point";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    public JoinPointRule() {

    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {

        PosInOccurrence pio = ruleApp.posInOccurrence();
        JoinRuleBuiltInRuleApp app = new JoinRuleBuiltInRuleApp(new JoinRule(),
                pio);

        MergePointStatement jPS = (MergePointStatement) JavaTools
                .getActiveStatement(
                        MergeRuleUtils.getJavaBlockRecursive(pio.subTerm()));

        ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = JoinRule
                .findPotentialJoinPartners(goal, pio, goal.proof().root());

        app.setJoinNode(goal.node());
        app.setConcreteRule(
                services.getSpecificationRepository().getJoinPointMergeSpec(jPS)
                        .getInstantiatedJoinProcedure(services));
        app.setJoinPartners(joinPartners);

        ImmutableList<Goal> newGoals = goal.split(1);
        Goal g = newGoals.head();
        newGoals = g.apply(app);

        return newGoals;
    }

    @Override
    public Name name() {
        return RULE_NAME;
    }

    @Override
    public String displayName() {
        return DISPLAY_NAME;
    }

    @Override
    public String toString() {
        return displayName();
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {

        if (pio != null && pio.subTerm().isContainsJavaBlockRecursive()
                && !goal.isLinked()
                && JavaTools.getActiveStatement(
                        TermBuilder.goBelowUpdates(pio.subTerm())
                                .javaBlock()) instanceof MergePointStatement) {

            MergePointStatement jps = ((MergePointStatement) JavaTools
                    .getActiveStatement(TermBuilder
                            .goBelowUpdates(pio.subTerm()).javaBlock()));

            ImmutableList<Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>>> joinPartners = JoinRule
                    .findPotentialJoinPartners(goal, pio);

            if (!joinPartners.isEmpty()) {

                ImmutableList<Goal> joinPartnersGoal = ImmutableSLList.nil();

                for (Triple<Goal, PosInOccurrence, HashMap<ProgramVariable, ProgramVariable>> p : joinPartners) {
                    joinPartnersGoal = joinPartnersGoal.append(p.first);
                }

                ImmutableList<Goal> openGoals = goal.node().proof().openGoals();
                for (Goal g : openGoals) {
                    if (!g.equals(goal) && !g.isLinked()
                            && !joinPartnersGoal.contains(g)
                            && containsNonActiveJPS(g, jps)) {
                        return false;
                    }
                }
                return true;
            }
        }
        return false;
    }

    /**
     * TODO
     * 
     * @param g
     * @param jps
     * @return
     */
    static boolean containsNonActiveJPS(Goal g, MergePointStatement jps) {
        return containsJPS(g, jps, true);
    }

    /**
     * TODO
     * 
     * @param g
     * @param jps
     * @return
     */
    static boolean containsJPS(Goal g, MergePointStatement jps) {
        return containsJPS(g, jps, false);
    }

    /**
     * TODO
     * 
     * @param g
     * @param jps
     * @param onlyNonActive
     * @return
     */
    private static boolean containsJPS(Goal g, MergePointStatement jps,
            boolean onlyNonActive) {
        for (SequentFormula sf : g.node().sequent().succedent()) {
            JavaBlock jb = MergeRuleUtils.getJavaBlockRecursive(sf.formula());

            if (jb.isEmpty()) {
                continue;
            }

            if (onlyNonActive && JavaTools.getActiveStatement(jb).equals(jps)) {
                return false;
            }

            Services services = g.proof().getServices();
            MethodFrame mf = JavaTools.getInnermostMethodFrame(jb, services);

            if (mf != null) {
                ContainsStatementVisitor visitor = new ContainsStatementVisitor(
                        mf, jps, services);
                visitor.start();
                return visitor.isContained();
            } else {
                return false;
            }
        }

        return false;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
            TermServices services) {
        return new JoinPointBuiltInRuleApp(this, pos);
    }
}
