/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.Optional;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.statement.SetStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;

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
    private final Name name;

    private SetStatementRule() {
        this.name = new Name("Set Statement");
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

    @NonNull
    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)
            throws RuleAbortException {
        if (!(ruleApp instanceof SetStatementBuiltInRuleApp)) {
            throw new IllegalArgumentException("can only apply SetStatementBuiltInRuleApp");
        }
        final TermBuilder tb = services.getTermBuilder();
        final PosInOccurrence occurrence = ruleApp.posInOccurrence();

        final Term formula = occurrence.subTerm();
        final Term update = UpdateApplication.getUpdate(formula);

        Term target;
        if (formula.op() instanceof UpdateApplication) {
            target = UpdateApplication.getTarget(formula);
        } else {
            target = formula;
        }

        final var setStatement =
            Optional.ofNullable(JavaTools.getActiveStatement(target.javaBlock()))
                    .filter(SetStatement.class::isInstance).map(SetStatement.class::cast)
                    .orElseThrow(() -> new RuleAbortException("not a Set Statement"));
        final CopyAssignment copy = KeYJavaASTFactory.assign(setStatement.getExpressionAt(0),
            setStatement.getExpressionAt(1), setStatement.getPositionInfo());

        final ImmutableList<Goal> result = goal.split(1);

        final var javaBlock =
            JavaTools.replaceStatement(target.javaBlock(), services, setStatement, copy);
        final var blockTerm = tb.prog((Modality) target.op(), javaBlock, target.sub(0), null);
        final var newTerm = tb.apply(update, blockTerm);
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
