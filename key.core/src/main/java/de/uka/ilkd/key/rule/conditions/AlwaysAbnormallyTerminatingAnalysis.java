/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.conditions;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Label;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.ast.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.ast.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.ast.expression.operator.BinaryOperatorKind;
import de.uka.ilkd.key.java.ast.statement.*;
import de.uka.ilkd.key.java.visitor.OuterBreakContinueAndReturnCollector;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/// Decides whether a statement cannot complete normally in the sense of JLS 14.22. Such a
/// statement always leaves the current flow of control abruptly, i.e. by a {@code return},
/// {@code throw}, {@code break}, {@code continue} or by not terminating at all.
///
/// The analysis is conservative: it may return {@code false} for a statement that actually cannot
/// complete normally, but it never claims that a statement cannot complete normally when it can.
/// This direction is required by the pattern-matching rules, which use the analysis to decide
/// whether a pattern variable is definitely bound after an {@code if} statement.
final class AlwaysAbnormallyTerminatingAnalysis {

    private final Services services;

    AlwaysAbnormallyTerminatingAnalysis(Services services) {
        this.services = services;
    }

    /// Returns whether the given statement cannot complete normally.
    boolean isAlwaysAbnormallyTerminating(@Nullable Statement statement) {
        if (statement == null) {
            return false;
        }
        return switch (statement) {
            case StatementBlock block -> isAlwaysAbnormallyTerminating(block.getBody());
            case Return ignored -> true;
            case Throw ignored -> true;
            case Break ignored -> true;
            case Continue ignored -> true;
            case If ifStmt -> ifStatement(ifStmt);
            case Try tryStmt -> tryStatement(tryStmt);
            case While whileStmt -> loopCannotCompleteNormally(whileStmt);
            case For forStmt -> loopCannotCompleteNormally(forStmt);
            case Do doStmt -> doStatement(doStmt);
            case EnhancedFor ignored -> false;
            case Switch switchStmt -> switchStatement(switchStmt);
            case LabeledStatement labeled -> labeledStatement(labeled);
            case SynchronizedBlock block -> isAlwaysAbnormallyTerminating(block.getBody());
            case LoopScopeBlock block -> isAlwaysAbnormallyTerminating(block.getBody());
            // JLS 14.22: an assert statement can complete normally if it is reachable, because
            // assertions may be disabled at runtime; the condition does not matter.
            case Assert ignored -> false;
            default -> false;
        };
    }

    /// Returns whether the given sequence cannot complete normally. This is the case as soon as
    /// one of its statements cannot complete normally.
    boolean isAlwaysAbnormallyTerminating(@Nullable ImmutableList<?> body) {
        if (body == null) {
            return false;
        }
        for (Object element : body) {
            if (element instanceof Statement statement
                    && isAlwaysAbnormallyTerminating(statement)) {
                return true;
            }
        }
        return false;
    }

    private boolean ifStatement(If ifStmt) {
        var elseBranch = ifStmt.getElse();
        if (alwaysTrue(ifStmt.getExpression())) {
            return isAlwaysAbnormallyTerminating(ifStmt.getThen());
        } else if (alwaysFalse(ifStmt.getExpression())) {
            return isAlwaysAbnormallyTerminating(elseBranch);
        }
        return isAlwaysAbnormallyTerminating(ifStmt.getThen())
                && isAlwaysAbnormallyTerminating(elseBranch);
    }

    private boolean tryStatement(Try tryStmt) {
        Finally finallyBranch = null;
        boolean allCatchesAbort = true;
        for (Branch branch : tryStmt.getBranchList()) {
            if (branch instanceof Finally f) {
                finallyBranch = f;
            } else if (!isAlwaysAbnormallyTerminating(branch)) {
                allCatchesAbort = false;
            }
        }
        if (isAlwaysAbnormallyTerminating(finallyBranch)) {
            return true;
        }
        return isAlwaysAbnormallyTerminating(tryStmt.getBody()) && allCatchesAbort;
    }

    /// A {@code while} or {@code for} loop cannot complete normally if its guard is always true
    /// and no {@code break} leaves the loop.
    private boolean loopCannotCompleteNormally(LoopStatement loop) {
        return guardIsAlwaysTrue(loop.getGuardExpression())
                && !hasUnlabeledBreak(loop.getBody());
    }

    /// A {@code do} loop executes its body at least once. It cannot complete normally if that
    /// body always aborts, or if the guard is always true and no {@code break} leaves the loop.
    /// A reachable {@code continue} that targets the loop transfers control to the condition, so
    /// the loop can complete normally when the condition is not the constant {@code true}
    /// (JLS 14.22).
    private boolean doStatement(Do doStmt) {
        if (hasUnlabeledBreak(doStmt.getBody())) {
            return false;
        }
        if (!guardIsAlwaysTrue(doStmt.getGuardExpression())
                && hasUnlabeledContinue(doStmt.getBody())) {
            return false;
        }
        return isAlwaysAbnormallyTerminating(doStmt.getBody())
                || guardIsAlwaysTrue(doStmt.getGuardExpression());
    }

    private boolean switchStatement(Switch switchStmt) {
        boolean hasDefault = false;
        for (Branch branch : switchStmt.getBranchList()) {
            if (branch instanceof Default) {
                hasDefault = true;
            }
            if (hasUnlabeledBreak(branch) || !isAlwaysAbnormallyTerminating(branch)) {
                return false;
            }
        }
        return hasDefault;
    }

    /// A labeled statement can complete normally if its body contains a {@code break} to that
    /// label. Otherwise it inherits the behavior of its body.
    private boolean labeledStatement(LabeledStatement labeled) {
        return !hasBreakTo(labeled.getBody(), labeled.getLabel())
                && isAlwaysAbnormallyTerminating(labeled.getBody());
    }

    private boolean isAlwaysAbnormallyTerminating(@Nullable Branch branch) {
        if (branch == null) {
            return false;
        }
        return switch (branch) {
            case Then then -> isAlwaysAbnormallyTerminating(then.getBody());
            case Else elseBranch -> isAlwaysAbnormallyTerminating(elseBranch.getBody());
            case Case caseBranch -> isAlwaysAbnormallyTerminating(caseBranch.getBody());
            case Default defaultBranch -> isAlwaysAbnormallyTerminating(defaultBranch.getBody());
            case Catch catchBranch -> isAlwaysAbnormallyTerminating(catchBranch.getBody());
            case Finally finallyBranch -> isAlwaysAbnormallyTerminating(finallyBranch.getBody());
            case Ccatch ccatch -> isAlwaysAbnormallyTerminating(ccatch.getBody());
            default -> false;
        };
    }

    /// Returns whether a {@code break} without a label leaves the given loop. Unlabeled breaks in
    /// nested loops or switches only leave those inner statements.
    private boolean hasUnlabeledBreak(Statement body) {
        var collector = new OuterBreakContinueAndReturnCollector(body, List.of(), services);
        collector.collect();
        return collector.getBreaks().stream().anyMatch(b -> b.getLabel() == null);
    }

    /// Returns whether a {@code continue} without a label targets the enclosing loop, i.e. it is
    /// not nested inside another loop within the given body.
    private boolean hasUnlabeledContinue(Statement body) {
        var collector = new OuterBreakContinueAndReturnCollector(body, List.of(), services);
        collector.collect();
        return !collector.getContinues().isEmpty();
    }

    private boolean hasUnlabeledBreak(Branch branch) {
        var body = switch (branch) {
            case Case caseBranch -> caseBranch.getBody();
            case Default defaultBranch -> defaultBranch.getBody();
            default -> null;
        };
        if (body == null) {
            return false;
        }
        for (Statement statement : body) {
            if (hasUnlabeledBreak(statement)) {
                return true;
            }
        }
        return false;
    }

    private boolean hasBreakTo(Statement body, Label label) {
        var collector = new OuterBreakContinueAndReturnCollector(body, List.of(), services);
        collector.collect();
        return collector.getBreaks().stream().anyMatch(b -> label.equals(b.getLabel()));
    }

    private boolean guardIsAlwaysTrue(@Nullable Expression guardExpression) {
        return guardExpression == null || alwaysTrue(guardExpression);
    }

    private boolean alwaysTrue(@Nullable Expression expression) {
        if (expression == null) {
            return false;
        }
        if (expression instanceof ParenthesizedExpression parenthesized) {
            return alwaysTrue(parenthesized.getExpressionAt(0));
        }
        if (expression instanceof BooleanLiteral literal) {
            return literal.getValue();
        }
        if (expression instanceof BinaryOperator operator) {
            if (operator.getKind() == BinaryOperatorKind.LOGICAL_AND) {
                return alwaysTrue(operator.getLeft()) && alwaysTrue(operator.getRight());
            } else if (operator.getKind() == BinaryOperatorKind.LOGICAL_OR) {
                return alwaysTrue(operator.getLeft()) || alwaysTrue(operator.getRight());
            }
        }
        return false;
    }

    private boolean alwaysFalse(@Nullable Expression expression) {
        if (expression == null) {
            return false;
        }
        if (expression instanceof ParenthesizedExpression parenthesized) {
            return alwaysFalse(parenthesized.getExpressionAt(0));
        }
        if (expression instanceof BooleanLiteral literal) {
            return !literal.getValue();
        }
        if (expression instanceof BinaryOperator operator) {
            if (operator.getKind() == BinaryOperatorKind.LOGICAL_AND) {
                return alwaysFalse(operator.getLeft()) || alwaysFalse(operator.getRight());
            } else if (operator.getKind() == BinaryOperatorKind.LOGICAL_OR) {
                return alwaysFalse(operator.getLeft()) && alwaysFalse(operator.getRight());
            }
        }
        return false;
    }
}
