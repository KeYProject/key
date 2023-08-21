/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.Optional;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.JmlAssert;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement.Kind;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.ImmutableList;

/**
 * A rule for JML assert/assume statements.
 *
 * This implements the rules as:
 *
 * <p>
 * {@code
 *    \DELTA => update(cond -> <.. ...>), \GAMMA
 * --------------------------------------------------------
 *    \DELTA => update(<.. //@assume cond; ...>), \GAMMA
 * }
 * </p>
 *
 * and
 *
 * <p>
 * {@code
 *    \DELTA => update(cond), \GAMMA   \DELTA => update(cond -> <.. ...>), \GAMMA
 * ---------------------------------------------------------------------------------
 *             \DELTA => update(<.. //@assert cond; ...>), \GAMMA
 * }
 * </p>
 *
 * @author Benjamin Takacs
 */
public final class JmlAssertRule implements BuiltInRule {

    /**
     * The instance for assert statements
     */
    public static final JmlAssertRule ASSERT_INSTANCE = new JmlAssertRule(Kind.ASSERT);
    /**
     * The instance for assume statements
     */
    public static final JmlAssertRule ASSUME_INSTANCE = new JmlAssertRule(Kind.ASSUME);
    /**
     * The name of this rule
     */
    private final Name name;
    /**
     * The kind of the matched jml assert statements (assert/assume)
     */
    private final Kind kind;

    private JmlAssertRule(final Kind kind) {
        this.kind = kind;
        this.name = new Name("JML " + kind.name().toLowerCase());
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
        return activeStatement instanceof JmlAssert
                && ((JmlAssert) activeStatement).getKind() == kind;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence occurrence, TermServices services) {
        return new JmlAssertBuiltInRuleApp(this, occurrence);
    }

    @Nonnull
    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)
            throws RuleAbortException {
        if (!(ruleApp instanceof JmlAssertBuiltInRuleApp)) {
            throw new IllegalArgumentException("can only apply JmlAssertBuiltInRuleApp");
        }
        final TermBuilder tb = services.getTermBuilder();
        final PosInOccurrence occurrence = ruleApp.posInOccurrence();

        final Term formula = occurrence.subTerm();
        final Term update = UpdateApplication.getUpdate(formula);

        Term target = formula;
        if (formula.op() instanceof UpdateApplication) {
            target = UpdateApplication.getTarget(formula);
        }

        final JmlAssert jmlAssert =
            Optional.ofNullable(JavaTools.getActiveStatement(target.javaBlock()))
                    .filter(JmlAssert.class::isInstance).map(JmlAssert.class::cast)
                    .orElseThrow(() -> new RuleAbortException("not a JML assert statement"));

        final MethodFrame frame = JavaTools.getInnermostMethodFrame(target.javaBlock(), services);
        final Term self = MiscTools.getSelfTerm(frame, services);

        final Term condition = jmlAssert.getCond(self, services);

        final ImmutableList<Goal> result;
        if (kind == Kind.ASSERT) {
            result = goal.split(2);
            setUpValidityRule(result.tail().head(), occurrence, update, condition, tb);
        } else if (kind == Kind.ASSUME) {
            result = goal.split(1);
        } else {
            throw new RuleAbortException(
                String.format("Unknown assertion type %s", jmlAssert.getKind()));
        }
        setUpUsageGoal(result.head(), occurrence, update, target, condition, tb, services);

        return result;
    }

    private void setUpValidityRule(Goal goal, PosInOccurrence occurrence, Term update,
            Term condition, TermBuilder tb) {
        goal.setBranchLabel("Validity");
        goal.changeFormula(new SequentFormula(tb.apply(update, condition)), occurrence);
    }

    private void setUpUsageGoal(Goal goal, PosInOccurrence occurrence, Term update, Term target,
            Term condition, TermBuilder tb, Services services) {
        goal.setBranchLabel("Usage");
        final JavaBlock javaBlock = JavaTools.removeActiveStatement(target.javaBlock(), services);
        final Term newTerm = tb.apply(update,
            tb.imp(condition, tb.prog((Modality) target.op(), javaBlock, target.sub(0), null)));

        goal.changeFormula(new SequentFormula(newTerm), occurrence);
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
