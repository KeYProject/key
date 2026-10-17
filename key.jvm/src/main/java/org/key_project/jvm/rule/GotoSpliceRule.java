/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm.rule;

import java.util.List;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.statement.LabeledStatement;
import de.uka.ilkd.key.java.ast.statement.MethodFrame;
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
 * Built-in rule that implements a <em>forward</em> JVM {@code goto}.
 * <p>
 * Applicable when the active statement is {@code local.goto_(pc)} with a constant int target
 * whose label {@code L<pc>} is still present in the remaining statement list of the innermost
 * method frame (a forward jump). Application deletes the range {@code [goto_, label)} and splices
 * the label body (without its guard) into place.
 */
public final class GotoSpliceRule implements BuiltInRule {

    public static final GotoSpliceRule INSTANCE = new GotoSpliceRule();

    private static final Name NAME = new Name("JVM Goto Splice (forward)");

    private GotoSpliceRule() {
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
        if (!GotoSupport.isGotoCall(activeStatement)) {
            return false;
        }
        try {
            String label = GotoSupport.labelOf(activeStatement);
            MethodFrame frame =
                JavaTools.getInnermostMethodFrame(target.javaBlock(), goal.getOverlayServices());
            return GotoSupport.forwardTarget(frame.getBody(), activeStatement, label) != null;
        } catch (RuleAbortException e) {
            return false;
        }
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
        String label = GotoSupport.labelOf(activeStatement);

        MethodFrame frame =
            JavaTools.getInnermostMethodFrame(target.javaBlock(), goal.getOverlayServices());
        LabeledStatement found = GotoSupport.forwardTarget(frame.getBody(), activeStatement, label);
        if (found == null) {
            throw new RuleAbortException(
                "GotoSpliceRule: label " + label + " is not ahead (use GotoRestoreRule).");
        }
        List<Statement> newStmts = GotoSupport.spliceBody(found, frame.getBody());
        return GotoSupport.reembedFrameBody(goal, ruleApp, newStmts);
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
