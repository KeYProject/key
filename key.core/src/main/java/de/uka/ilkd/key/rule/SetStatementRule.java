/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.Optional;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.SetStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

/**
 * A rule for set statements. This unwraps the contained CopyAssignment
 *
 * @author Julian Wiesler
 */
public final class SetStatementRule implements BuiltInRule {

    /**
     * The instance
     */
    public static final SetStatementRule INSTANCE = new SetStatementRule();
    /**
     * The name of this rule
     */
    private static final Name name = new Name("Set Statement");

    private SetStatementRule() {
        // no statements
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence occurrence) {
        if (AbstractAuxiliaryContractRule.occursNotAtTopLevelInSuccedent(occurrence)) {
            return false;
        }
        // abort if inside of transformer
        if (Transformer.inTransformer(occurrence)) {
            return false;
        }

        Term target = occurrence.subTerm();
        if (target.op() instanceof UpdateApplication) {
            target = UpdateApplication.getTarget(target);
        }
        final SourceElement activeStatement = JavaTools.getActiveStatement(target.javaBlock());
        return activeStatement instanceof SetStatement;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence occurrence, TermServices services) {
        return new SetStatementBuiltInRuleApp(this, occurrence);
    }

    @Override
    public @NonNull ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)
            throws RuleAbortException {
        if (!(ruleApp instanceof SetStatementBuiltInRuleApp)) {
            throw new IllegalArgumentException("can only apply SetStatementBuiltInRuleApp");
        }

        final TermBuilder tb = services.getTermBuilder();
        final PosInOccurrence occurrence = ruleApp.posInOccurrence();
        final Term formula = occurrence.subTerm();
        assert formula.op() instanceof UpdateApplication
                : "Currently, this can only be applied if there is an update application in front of the modality";

        Term update = UpdateApplication.getUpdate(formula);
        Term target = UpdateApplication.getTarget(formula);

        SetStatement setStatement =
            Optional.ofNullable(JavaTools.getActiveStatement(target.javaBlock()))
                    .filter(SetStatement.class::isInstance).map(SetStatement.class::cast)
                    .orElseThrow(() -> new RuleAbortException("not a JML set statement."));

        final MethodFrame frame = JavaTools.getInnermostMethodFrame(target.javaBlock(), services);
        final Term self = MiscTools.getSelfTerm(frame, services);

        var spec = services.getSpecificationRepository().getStatementSpec(setStatement);

        if (spec == null) {
            throw new RuleAbortException(
                "No specification for the set statement found in the specification repository.");
        }

        var targetTerm = spec.getTerm(services, self, SetStatement.INDEX_TARGET);
        var valueTerm = spec.getTerm(services, self, SetStatement.INDEX_VALUE);

        Term newUpdate = tb.elementary(targetTerm, valueTerm);

        JavaBlock javaBlock = JavaTools.removeActiveStatement(target.javaBlock(), services);

        Term term =
            tb.prog(((Modality) target.op()).kind(), javaBlock, target.sub(0), target.getLabels());
        Term newTerm = tb.apply(update, tb.apply(newUpdate, term));

        ImmutableList<Goal> result = goal.split(1);
        result.head().changeFormula(new SequentFormula(newTerm), occurrence);
        return result;
    }

    @Override
    public Name name() {
        return name;
    }

    @Override
    public String displayName() {
        return name.toString();
    }

    @Override
    public String toString() {
        return name.toString();
    }
}
