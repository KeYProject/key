/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm.rule;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.ast.statement.If;
import de.uka.ilkd.key.java.ast.statement.Then;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

import org.key_project.logic.Name;
import org.key_project.logic.op.Modality;
import org.key_project.prover.rules.RuleAbortException;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

/**
 * Built-in rule that unwraps constant-condition {@code if} statements that the transpiler emits
 * for reachability and label guards:
 * <ul>
 * <li>{@code if (true) { S }} → {@code S} (mid-layout {@code return}/{@code throw} wrappers)</li>
 * <li>{@code if (false) { break L; }} → {@code {}} (label guards, cleaned up by
 * {@code blockEmpty})</li>
 * </ul>
 * The transpiler only emits literal conditions in these two shapes, so any Nr-lit condition can be
 * unwrapped unconditionally.
 */
public final class IfLiteralRule implements BuiltInRule {

    public static final IfLiteralRule INSTANCE = new IfLiteralRule();

    private static final Name NAME = new Name("JVM If-Literal unwrap");

    private IfLiteralRule() {
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence occurrence) {
        if (GotoSupport.occursNotAtTopLevelInSuccedent(occurrence)
                || Transformer.inTransformer(occurrence)) {
            return false;
        }
        JTerm target = GotoSupport.modalityTarget(occurrence);
        if (!(target.op() instanceof Modality)) {
            return false;
        }
        final SourceElement activeStatement = JavaTools.getActiveStatement(target.javaBlock());
        return activeStatement instanceof If iff && iff.getExpression() instanceof BooleanLiteral;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence occurrence, TermServices services) {
        return new JvmBuiltInRuleApp(this, occurrence);
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, RuleApp ruleApp) throws RuleAbortException {
        JTerm target = GotoSupport.modalityTarget(ruleApp.posInOccurrence());
        final SourceElement activeStatement = JavaTools.getActiveStatement(target.javaBlock());
        if (!(activeStatement instanceof If iff)) {
            throw new RuleAbortException("IfLiteralRule: active statement is not an if.");
        }
        if (!(iff.getExpression() instanceof BooleanLiteral literal)) {
            throw new RuleAbortException("IfLiteralRule: guard is not a literal.");
        }

        Statement replacement;
        if (literal.getValue()) {
            Then then = iff.getThen();
            replacement = then == null ? new StatementBlock() : then.getBody();
        } else {
            replacement = iff.getElse() == null ? new StatementBlock() : iff.getElse().getBody();
        }

        return GotoSupport.reembedReplacing(goal, ruleApp, iff, replacement);
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public String displayName() {
        return NAME.toString();
    }

    @Override
    public String toString() {
        return NAME.toString();
    }
}
