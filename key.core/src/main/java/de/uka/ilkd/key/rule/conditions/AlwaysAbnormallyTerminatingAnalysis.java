/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Label;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.ast.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.ast.expression.operator.BinaryOperatorKind;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.statement.*;

import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.Nullable;

/// This analysis returns true iff a statement has the possibility to terminate normally
/// iff not every run terminates abnormally.
///
class AlwaysAbnormallyTerminatingAnalysis {

    record TerminationReason(boolean isReturn, Set<KeYJavaType> isThrow, String breakTo,
            String continueTo) {
        public TerminationReason(boolean isReturn) {
            this(isReturn, Set.of(), null, null);
        }

        public TerminationReason(KeYJavaType keYJavaType) {
            this(false, Set.of(keYJavaType), null, null);
        }

        public boolean isAbnormallTerminating() {
            return isReturn || !isThrow.isEmpty() || breakTo != null && continueTo != null;
        }
    }

    private final KeYJavaType assertionException;
    private final LinkedList<Label> labelStack = new LinkedList<>();
    private final ExecutionContext ec;
    private final Services services;

    AlwaysAbnormallyTerminatingAnalysis(ExecutionContext ec, Services services) {
        this.ec = ec;
        this.services = services;

        assertionException = services.getJavaInfo().getKeYJavaType("java.lang.AssertionError");
    }

    public @Nullable TerminationReason abnormallyTerminating(Statement stmt) {
        return switch (stmt) {
            case EnhancedFor forStmt -> abnormallyTerminating(forStmt.getBody());
            case Do doStmt -> abnormallyTerminating(doStmt.getBody());
            case For forStmt -> abnormallyTerminating(forStmt.getBody());
            case Switch switchStmt -> {
                if (hasDefaultBranch(switchStmt)) {
                    yield allAbnormallyTerminating(switchStmt.getBranchList());
                }
                yield null;
            }
            case If ifStmt -> //
                alwaysTrue(ifStmt.getExpression())
                        ? abnormallyTerminating(ifStmt.getThen())
                        : alwaysFalse(ifStmt.getExpression())
                                ? abnormallyTerminating(ifStmt.getElse())
                                : and(abnormallyTerminating(ifStmt.getThen()),
                                    abnormallyTerminating(ifStmt.getElse()));

            case Try tStmt -> {
                var s1 = abnormallyTerminating(tStmt.getBody());
                var s2 = removeCatchClauses(s1, tStmt.getBranchList());
                yield isAbnormallTerminating(s2) ? s2 : null;
            }
            case While wStmt -> abnormallyTerminating(wStmt.getBody());
            case Assert aStmt ->
                alwaysFalse(aStmt.getCondition()) ? new TerminationReason(assertionException)
                        : null;
            case StatementBlock b -> abnormallyTerminating(b.getBody());
            case Continue cStmt ->
                new TerminationReason(false, Set.of(), null,
                    cStmt.getLabel() == null ? "" : cStmt.getLabel().toString());
            case Break bStmt ->
                new TerminationReason(false, Set.of(),
                    bStmt.getLabel() == null ? "" : bStmt.getLabel().toString(), null);
            case Return ret -> new TerminationReason(true);
            case Throw thr -> {
                yield new TerminationReason(thr.getExpression().getKeYJavaType(services, ec));
            }
            case LabeledStatement ignored1 -> {
                labelStack.addLast(ignored1.getLabel());
                var b = abnormallyTerminating(ignored1.getBody());
                labelStack.removeLast();
                yield b;
            }
            case SynchronizedBlock s -> abnormallyTerminating(s.getBody());
            case LoopScopeBlock s -> abnormallyTerminating(s.getBody());
            default -> null;
        };
    }

    private boolean hasDefaultBranch(Switch switchStmt) {
        return switchStmt.getBranchList().stream().anyMatch(it -> it instanceof Default);
    }

    private TerminationReason removeCatchClauses(@Nullable TerminationReason s1,
            ImmutableArray<Branch> branchList) {
        var exc = new HashSet<>(s1 == null ? Set.of() : s1.isThrow);
        var newExcCatch = new HashSet<KeYJavaType>();
        final var isReturn = s1 != null && s1.isReturn;

        var catchReturns = true;

        boolean finallyReturn = false;
        for (var branch : branchList) {
            if (branch instanceof Catch c) {
                var t =
                    (KeYJavaType) c.getParameterDeclaration().getVariableSpecification().getType();
                exc.remove(t);
                var q = abnormallyTerminating(c);
                if (q != null) {
                    newExcCatch.addAll(q.isThrow);
                    catchReturns = catchReturns && q.isReturn;
                } else {
                    catchReturns = false;
                }
            }
            if (branch instanceof Finally f) {
                var q = abnormallyTerminating(f);
                if (q != null) {
                    newExcCatch.addAll(q.isThrow);
                    finallyReturn = q.isReturn;
                } else {
                    finallyReturn = false;
                }
            }
        }

        exc.addAll(newExcCatch);
        var ret = finallyReturn || isReturn && (!s1.isThrow().isEmpty() && catchReturns);
        return new TerminationReason(ret, exc, s1 == null ? null : s1.breakTo,
            s1 == null ? null : s1.continueTo);
    }

    private boolean isAbnormallTerminatingOnlyException(TerminationReason s1) {
        return s1 != null && !s1.isThrow.isEmpty() && s1.isReturn;
    }

    private boolean isAbnormallTerminating(TerminationReason b) {
        return b != null && b.isAbnormallTerminating();
    }

    private @Nullable TerminationReason or(@Nullable TerminationReason a, TerminationReason b) {
        final var a1 = isAbnormallTerminating(a);
        final var b1 = isAbnormallTerminating(b);
        if (a1 && b1) {
            var s = new HashSet<>(a.isThrow);
            s.addAll(b.isThrow);
            return new TerminationReason(a.isReturn || b.isReturn, s, a.breakTo, a.continueTo);
        } else if (a1) {
            return a;
        } else if (b1) {
            return b;
        }
        return null;
    }

    private @Nullable TerminationReason and(@Nullable TerminationReason a,
            @Nullable TerminationReason b) {
        if (a != null && a.isAbnormallTerminating()
                && b != null && b.isAbnormallTerminating()) {
            var s = new HashSet<>(a.isThrow);
            s.addAll(b.isThrow);
            return new TerminationReason(a.isReturn || b.isReturn, s, a.breakTo, a.continueTo);
        }
        return null;
    }

    private TerminationReason abnormallyTerminatingFinally(ImmutableArray<Branch> branchList) {
        for (var branch : branchList) {
            if (branch instanceof Finally) {
                return abnormallyTerminating(branch);
            }
        }
        return null;
    }


    private boolean alwaysTrue(@Nullable Expression guardExpression) {
        if (guardExpression == null)
            return false;
        if (guardExpression instanceof BooleanLiteral bl) {
            return bl.getValue();
        } else if (guardExpression instanceof BinaryOperator bo) {
            if (bo.getKind() == BinaryOperatorKind.LOGICAL_AND) {
                return alwaysTrue(bo.getLeft()) && alwaysTrue(bo.getRight());
            } else if (bo.getKind() == BinaryOperatorKind.LOGICAL_OR) {
                return alwaysTrue(bo.getLeft()) || alwaysTrue(bo.getRight());
            }
        }
        return false;
    }

    private boolean alwaysFalse(@Nullable Expression guardExpression) {
        if (guardExpression == null)
            return false;
        if (guardExpression instanceof BooleanLiteral bl) {
            return !bl.getValue();
        } else if (guardExpression instanceof BinaryOperator bo) {
            if (bo.getKind() == BinaryOperatorKind.LOGICAL_AND) {
                return alwaysFalse(bo.getLeft()) && alwaysFalse(bo.getRight());
            } else if (bo.getKind() == BinaryOperatorKind.LOGICAL_OR) {
                return alwaysFalse(bo.getLeft()) || alwaysFalse(bo.getRight());
            }
        }
        return false;
    }

    private TerminationReason allAbnormallyTerminating(ImmutableArray<Branch> branchList) {
        return branchList.stream().map(this::abnormallyTerminating)
                .reduce(this::and).orElse(null);
    }

    private TerminationReason abnormallyTerminating(ImmutableArray<? extends Statement> body) {
        for (var statement : body) {
            final var terminationReason = abnormallyTerminating(statement);
            if (terminationReason != null && terminationReason.isAbnormallTerminating())
                return terminationReason;
        }
        return null;
    }

    private @Nullable TerminationReason abnormallyTerminating(@Nullable Branch it) {
        if (it == null)
            return null;
        return switch (it) {
            case Finally f -> abnormallyTerminating(f.getBody());
            case Case f -> abnormallyTerminating(f.getBody());
            case Default f -> abnormallyTerminating(f.getBody());
            case Ccatch f -> abnormallyTerminating(f.getBody());
            case Then f -> abnormallyTerminating(f.getBody());
            case Else f -> abnormallyTerminating(f.getBody());
            case Catch f -> abnormallyTerminating(f.getBody());
            default -> null;
        };
    }

}
