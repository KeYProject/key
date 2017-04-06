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

import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * TODO
 *
 * @author Dominic Scheurer
 */
public class DeleteMergePointRule implements BuiltInRule {

    public static final DeleteMergePointRule INSTANCE = new DeleteMergePointRule();

    private static final String DISPLAY_NAME = "Delete Merge Point";
    private static final Name RULE_NAME = new Name(DISPLAY_NAME);

    public DeleteMergePointRule() {

    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) throws RuleAbortException {
        final TermBuilder tb = services.getTermBuilder();

        final ImmutableList<Goal> goals = goal.split(1);
        goal = goals.head();
        final PosInOccurrence pio = ruleApp.posInOccurrence();
        final Term formula = pio.topLevel().subTerm();
        final Term target = TermBuilder.goBelowUpdates(formula);
        final JavaBlock newJavaBlock = JavaTools
                .removeActiveStatement(target.javaBlock(), services);
        final Term newFormula = tb.prog((Modality) target.op(), newJavaBlock,
                target.sub(0));

        goal.changeFormula(new SequentFormula(tb
                .apply(UpdateApplication.getUpdate(formula), newFormula)),
                pio);
        
        return goals;
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

        if (pio == null || !pio.subTerm().isContainsJavaBlockRecursive()) {
            return false;
        }

        SourceElement activeStatement = JavaTools.getActiveStatement(
                TermBuilder.goBelowUpdates(pio.subTerm()).javaBlock());

        if (!(activeStatement instanceof MergePointStatement)) {
            return false;
        }

        MergePointStatement jps = ((MergePointStatement) activeStatement);

        boolean result = StreamSupport
                .stream(goal.proof().openGoals().spliterator(), true)
                .filter(g -> g != goal && !g.isLinked())
                .filter(g -> MergePointRule.containsMPS(g, jps))
                .collect(Collectors.counting()).intValue() == 0;
        return result;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
            TermServices services) {
        return new DeleteMergePointBuiltInRuleApp(this, pos);
    }

}
