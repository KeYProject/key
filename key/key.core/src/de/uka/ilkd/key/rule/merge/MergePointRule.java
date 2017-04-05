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

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.ContainsStatementVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.MergeContract;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
public class MergePointRule implements BuiltInRule {
    public static final MergePointRule INSTANCE = new MergePointRule();

    private static final String DISPLAY_NAME = "Merge Point Rule";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    public MergePointRule() {

    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {

        PosInOccurrence pio = ruleApp.posInOccurrence();
        MergeRuleBuiltInRuleApp app = new MergeRuleBuiltInRuleApp(
                MergeRule.INSTANCE, pio);

        MergePointStatement mps = (MergePointStatement) JavaTools
                .getActiveStatement(
                        MergeRuleUtils.getJavaBlockRecursive(pio.subTerm()));

        ImmutableList<MergePartner> mergePartners = MergeRule
                .findPotentialMergePartners(goal, pio, goal.proof().root());

        app.setMergeNode(goal.node());
        final ImmutableSet<MergeContract> mergeContracts = services
                .getSpecificationRepository().getMergeContracts(mps);

        assert mergeContracts != null && mergeContracts
                .size() == 1 : "There should be exactly one MergeContract for each MergePointStatement";

        app.setConcreteRule(mergeContracts.iterator().next()
                .getInstantiatedMergeProcedure());
        app.setMergePartners(mergePartners);

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

            ImmutableList<MergePartner> mergePartners = MergeRule
                    .findPotentialMergePartners(goal, pio);

            if (!mergePartners.isEmpty()) {

                ImmutableList<Goal> emrgePartnersGoal = ImmutableSLList.nil();

                for (MergePartner p : mergePartners) {
                    emrgePartnersGoal = emrgePartnersGoal.append(p.getGoal());
                }

                ImmutableList<Goal> openGoals = goal.node().proof().openGoals();
                for (Goal g : openGoals) {
                    if (!g.equals(goal) && !g.isLinked()
                            && !emrgePartnersGoal.contains(g)
                            && containsNonActiveMPS(g, jps)) {
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
    static boolean containsNonActiveMPS(Goal g, MergePointStatement jps) {
        return containsMPS(g, jps, true);
    }

    /**
     * TODO
     * 
     * @param g
     * @param jps
     * @return
     */
    static boolean containsMPS(Goal g, MergePointStatement jps) {
        return containsMPS(g, jps, false);
    }

    /**
     * TODO
     * 
     * @param g
     * @param jps
     * @param onlyNonActive
     * @return
     */
    private static boolean containsMPS(Goal g, MergePointStatement jps,
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
        return new MergePointBuiltInRuleApp(this, pos);
    }
}
