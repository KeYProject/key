/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm.rule;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Label;
import de.uka.ilkd.key.java.ast.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.ast.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.ast.reference.MethodReference;
import de.uka.ilkd.key.java.ast.statement.Break;
import de.uka.ilkd.key.java.ast.statement.If;
import de.uka.ilkd.key.java.ast.statement.LabeledStatement;
import de.uka.ilkd.key.java.ast.statement.MethodFrame;
import de.uka.ilkd.key.java.ast.statement.Then;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.op.Modality;
import org.key_project.prover.rules.RuleAbortException;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

/**
 * Shared machinery of the JVM {@code goto} built-in rules: recognizing {@code local.goto_(pc)}
 * calls, locating their target labels (forward in the current frame body vs. backward), splicing
 * the label content into place, and re-embedding the resulting program into the goal's modality
 * term.
 */
final class GotoSupport {

    private GotoSupport() {
    }

    /** Is the active element a {@code local.goto_("...")} method call? */
    static boolean isGotoCall(SourceElement active) {
        return active instanceof MethodReference mr
                && "goto_".equals(mr.getMethodName().toString());
    }

    /** Extracts the target label name (as {@code L<pc>}) from the active {@code goto_} call. */
    static String labelOf(SourceElement active) throws RuleAbortException {
        if (!(active instanceof MethodReference mr) || !isGotoCall(active)) {
            throw new RuleAbortException("active statement is not local.goto_(...)");
        }
        if (mr.getArguments().size() != 1) {
            throw new RuleAbortException("goto_ expects exactly one (constant int) argument");
        }
        if (!(mr.getArgumentAt(0) instanceof IntLiteral literal)) {
            throw new RuleAbortException(
                "goto_ target must be a constant int literal, got "
                    + mr.getArgumentAt(0).getClass().getSimpleName());
        }
        return "L" + literal.getValue();
    }

    /** The label statement which is still ahead of the active statement in the frame body. */
    static LabeledStatement forwardTarget(StatementBlock body, SourceElement active, String label) {
        var stmts = body.getBody();
        for (int i = 0; i < stmts.size(); i++) {
            if (contains(stmts.get(i), active)) {
                for (int j = i + 1; j < stmts.size(); j++) {
                    if (stmts.get(j) instanceof LabeledStatement ls
                            && labelOf(ls).equals(label)) {
                        return ls;
                    }
                }
                return null;
            }
        }
        return null;
    }

    /** The first top-level label statement with the given name in a body (any position). */
    static LabeledStatement findTarget(StatementBlock body, String label) {
        for (Statement s : body.getBody()) {
            if (s instanceof LabeledStatement ls && labelOf(ls).equals(label)) {
                return ls;
            }
        }
        return null;
    }

    /**
     * The replacement statement list for a jump to {@code target}: the content of the target label
     * statement (without its literal guard) followed by the statements after it in {@code source}.
     */
    static List<Statement> spliceBody(LabeledStatement target, StatementBlock source) {
        List<Statement> result = new ArrayList<>();
        if (target.getBody() instanceof StatementBlock inner) {
            var stmts = inner.getBody();
            String label = labelOf(target);
            int start = stmts.size() > 0 && isGuard(stmts.get(0), label) ? 1 : 0;
            for (int i = start; i < stmts.size(); i++) {
                result.add(stmts.get(i));
            }
        }
        boolean afterTarget = false;
        for (Statement s : source.getBody()) {
            if (s == target) {
                afterTarget = true;
                continue;
            }
            if (afterTarget) {
                result.add(s);
            }
        }
        return result;
    }

    /** Recognizes the transpiler's label guard {@code if (false) { break <label>; }}. */
    static boolean isGuard(Statement s, String label) {
        if (!(s instanceof If iff)) {
            return false;
        }
        if (!(iff.getExpression() instanceof BooleanLiteral literal) || literal.getValue()) {
            return false;
        }
        Then then = iff.getThen();
        if (then == null || then.getStatementCount() != 1) {
            return false;
        }
        Statement body = then.getStatementAt(0);
        if (body instanceof StatementBlock block && block.getStatementCount() == 1) {
            body = block.getStatementAt(0);
        }
        if (!(body instanceof Break br)) {
            return false;
        }
        Label l = br.getLabel();
        return l != null && l.toString().equals(label);
    }

    /** Unwraps a leading update application and returns the enclosed modality term, if any. */
    static JTerm modalityTarget(PosInOccurrence occurrence) {
        JTerm t = (JTerm) occurrence.subTerm();
        if (t.op() instanceof UpdateApplication) {
            t = UpdateApplication.getTarget(t);
        }
        return t;
    }

    /** The JVM rules are applied at the top level of the succedent only. */
    static boolean occursNotAtTopLevelInSuccedent(PosInOccurrence occurrence) {
        return occurrence == null || !occurrence.isTopLevel() || occurrence.isInAntec();
    }

    static boolean contains(SourceElement root, SourceElement needle) {
        if (root == needle) {
            return true;
        }
        if (root instanceof NonTerminalProgramElement pe) {
            for (int i = 0; i < pe.getChildCount(); i++) {
                if (contains(pe.getChildAt(i), needle)) {
                    return true;
                }
            }
        }
        return false;
    }

    static String labelOf(LabeledStatement ls) {
        ProgramElementName pen = ls.getProgramElementName();
        return pen != null ? pen.toString() : ls.getLabel().toString();
    }

    /**
     * Rebuilds the modality term around {@code newJb} and installs it in the goal, mirroring
     * {@code SetStatementRule}. Expects an update application in front of the modality (as produced
     * by the proof initialization for method contracts).
     */
    static ImmutableList<Goal> reembed(Goal goal, RuleApp ruleApp, JavaBlock newJb)
            throws RuleAbortException {
        Services services = goal.getOverlayServices();
        TermBuilder tb = services.getTermBuilder();
        PosInOccurrence occurrence = ruleApp.posInOccurrence();
        JTerm formula = (JTerm) occurrence.subTerm();
        if (!(formula.op() instanceof UpdateApplication)) {
            throw new RuleAbortException(
                "Expected an update application in front of the modality.");
        }
        JTerm update = UpdateApplication.getUpdate(formula);
        JTerm target = UpdateApplication.getTarget(formula);

        JTerm term =
            tb.prog(((Modality) target.op()).kind(), newJb, target.sub(0), target.getLabels());
        JTerm newTerm = tb.apply(update, term);

        ImmutableList<Goal> result = goal.split(1);
        result.head().changeFormula(new SequentFormula(newTerm), occurrence);
        return result;
    }

    /** Replaces the innermost method frame's body by a new statement list (goto rules). */
    static ImmutableList<Goal> reembedFrameBody(Goal goal, RuleApp ruleApp,
            List<Statement> newStmts)
            throws RuleAbortException {
        Services services = goal.getOverlayServices();
        JTerm target = GotoSupport.modalityTarget(ruleApp.posInOccurrence());
        MethodFrame frame = JavaTools.getInnermostMethodFrame(target.javaBlock(), services);
        if (frame == null) {
            throw new RuleAbortException("No innermost method frame found.");
        }
        StatementBlock newBody = new StatementBlock(newStmts.toArray(new Statement[0]));
        JavaBlock newJb =
            JavaTools.replaceStatement(target.javaBlock(), services, frame.getBody(), newBody);
        return reembed(goal, ruleApp, newJb);
    }

    /**
     * Replaces a single program statement (e.g. a constant-condition if) by {@code replacement}.
     */
    static ImmutableList<Goal> reembedReplacing(Goal goal, RuleApp ruleApp, SourceElement old,
            SourceElement replacement) throws RuleAbortException {
        Services services = goal.getOverlayServices();
        JTerm target = GotoSupport.modalityTarget(ruleApp.posInOccurrence());
        JavaBlock newJb =
            JavaTools.replaceStatement(target.javaBlock(), services, old, replacement);
        return reembed(goal, ruleApp, newJb);
    }
}
