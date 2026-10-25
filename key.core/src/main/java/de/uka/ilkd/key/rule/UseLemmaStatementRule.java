/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.Optional;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.statement.MethodFrame;
import de.uka.ilkd.key.java.ast.statement.UseLemmaStatement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.op.Modality;
import org.key_project.prover.rules.RuleAbortException;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

/**
 * A rule for use_lemma statements. This turns a statement `use_lemma lemma(x)` to an assumption
 * `lemma(x) = TRUE` which allows rules to be applied that set the expand the contract.
 *
 * @author Mattias Ulbrich
 */
public final class UseLemmaStatementRule implements BuiltInRule {

    /**
     * The instance
     */
    public static final UseLemmaStatementRule INSTANCE = new UseLemmaStatementRule();

    /**
     * The name of this rule
     */
    private static final Name name = new Name("Use Lemma Statement");

    private UseLemmaStatementRule() {
        // no statements
    }

    @Override
    public boolean isApplicable(Goal goal,
            PosInOccurrence occurrence) {
        if (AbstractAuxiliaryContractRule.occursNotAtTopLevelInSuccedent(occurrence)) {
            return false;
        }
        // abort if inside of transformer
        if (Transformer.inTransformer(occurrence)) {
            return false;
        }

        JTerm target = (JTerm) occurrence.subTerm();
        if (target.op() instanceof UpdateApplication) {
            target = UpdateApplication.getTarget(target);
        }
        final SourceElement activeStatement = JavaTools.getActiveStatement(target.javaBlock());
        return activeStatement instanceof UseLemmaStatement;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence occurrence, TermServices services) {
        return new UseLemmaStatementBuiltInRuleApp(this, occurrence);
    }

    @Override
    public @NonNull ImmutableList<Goal> apply(Goal goal, RuleApp ruleApp)
            throws RuleAbortException {
        if (!(ruleApp instanceof UseLemmaStatementBuiltInRuleApp)) {
            throw new IllegalArgumentException("can only apply UseLemmaStatementBuiltInRuleApp");
        }

        final var services = goal.getOverlayServices();
        final TermBuilder tb = services.getTermBuilder();
        final PosInOccurrence occurrence = ruleApp.posInOccurrence();
        final JTerm formula = (JTerm) occurrence.subTerm();
        assert formula.op() instanceof UpdateApplication
                : "Currently, this can only be applied if there is an update application in front of the modality";

        JTerm update = UpdateApplication.getUpdate(formula);
        JTerm target = UpdateApplication.getTarget(formula);

        UseLemmaStatement useLemmaStatement =
            Optional.ofNullable(JavaTools.getActiveStatement(target.javaBlock()))
                    .filter(UseLemmaStatement.class::isInstance).map(UseLemmaStatement.class::cast)
                    .orElseThrow(() -> new RuleAbortException("not a JML set statement."));

        final MethodFrame frame = JavaTools.getInnermostMethodFrame(target.javaBlock(), services);
        final JTerm self = MiscTools.getSelfTerm(frame, services);

        var spec = services.getSpecificationRepository().getStatementSpec(useLemmaStatement);

        if (spec == null) {
            throw new RuleAbortException(
                "No specification for the set statement found in the specification repository.");
        }

        var targetTerm = spec.getTerm(services, self, 0);
        var assumption = tb.equals(targetTerm, tb.TRUE());

        assert targetTerm.op() instanceof ProgramMethod pm && pm.isLemma();

        JTerm updatedAssumption = tb.apply(update, assumption);

        JavaBlock javaBlock = JavaTools.removeActiveStatement(target.javaBlock(), services);

        JTerm term =
            tb.prog(((Modality) target.op()).kind(), javaBlock, target.sub(0), target.getLabels());
        JTerm newTerm = tb.apply(update, term);

        ImmutableList<Goal> result = goal.split(1);
        result.head().changeFormula(new SequentFormula(newTerm), occurrence);
        result.head().addFormula(new SequentFormula(updatedAssumption), true, true);
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
