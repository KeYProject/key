/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import java.util.*;

import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.ast.expression.operator.*;
import de.uka.ilkd.key.logic.op.LocationVariable;

/**
 *
 * @author Alexander Weigl
 * @version 1 (20.08.26)
 */
public class BindingVariableVisitor {
    public record Bindings(Map<LocationVariable, Expression> whenTrue,
            Map<LocationVariable, Expression> whenFalse) {
        public Bindings(Map<LocationVariable, Expression> whenTrue,
                Map<LocationVariable, Expression> whenFalse) {
            this.whenTrue = Collections.unmodifiableMap(whenTrue);
            this.whenFalse = Collections.unmodifiableMap(whenFalse);
        }

        static Bindings empty() {
            return new Bindings(Map.of(), Map.of());
        }

        @Override
        public String toString() {
            return "Bindings{whenTrue=" + whenTrue + ", whenFalse=" + whenFalse + "}";
        }
    }

    public static Bindings analyze(Expression e) {
        if (e instanceof InstanceofPattern io) {
            // §6.3.1.5 — a instanceof p
            // "when true" = variables declared by p. No "when false" rule:
            // it can't be determined at compile time that the match failed
            // in a way that still binds anything.
            var name = (LocationVariable) io.getPatternVariable().getProgramVariable();
            var expr = io.getExpressionAt(0);
            return new Bindings(Map.of(name, expr), Map.of());
        } else if (e instanceof BinaryOperator bo) {
            if (bo.getKind() == BinaryOperatorKind.LOGICAL_AND) {
                // §6.3.1.1 — a && b
                Bindings a = analyze(bo.getExpressionAt(0));
                Bindings b = analyze(bo.getExpressionAt(1));

                requireDisjoint(a.whenTrue, b.whenTrue,
                    "both operands of && declare pattern variable when true");
                requireDisjoint(a.whenFalse, b.whenFalse,
                    "both operands of && declare pattern variable when false");

                // a's "when true" set is definitely matched at b (scope flows rightward).
                var whenTrue = union(a.whenTrue, b.whenTrue);
                // No rule for a && b when false: can't tell at compile time which
                // operand caused the false result.
                return new Bindings(whenTrue, Map.of());
            } else if (bo.getKind() == BinaryOperatorKind.LOGICAL_OR) {
                // §6.3.1.2 — a || b (mirror image of &&)
                Bindings a = analyze(bo.getExpressionAt(0));
                Bindings b = analyze(bo.getExpressionAt(1));

                requireDisjoint(a.whenTrue, b.whenTrue,
                    "both operands of || declare pattern variable when true");
                requireDisjoint(a.whenFalse, b.whenFalse,
                    "both operands of || declare pattern variable when false");
                // a's "when false" set is definitely matched at b.
                var whenFalse = union(a.whenFalse, b.whenFalse);
                // No rule for a || b when true.
                return new Bindings(Map.of(), whenFalse);
            }
        } else if (e instanceof UnaryOperator not && not.kind == UnaryOperatorKind.LOGICAL_NOT) {
            // §6.3.1.3 — !a: true/false swap.
            Bindings a = analyze(not.getExpressionAt(0));
            return new Bindings(a.whenFalse, a.whenTrue);
        } else if (e instanceof Conditional c) {
            // §6.3.1.4 — a ? b : c
            Bindings condB = analyze(c.getExpressionAt(0));
            Bindings thenB = analyze(c.getExpressionAt(1));
            Bindings elseB = analyze(c.getExpressionAt(2));
            // (condB.whenTrue is definitely matched at b; condB.whenFalse at c —
            // see DefinitelyMatchedAt below if you need those sets directly.)

            requireDisjoint(condB.whenTrue, elseB.whenTrue,
                "cond(true) and else-branch(true) both declare pattern variable");
            requireDisjoint(condB.whenTrue, elseB.whenFalse,
                "cond(true) and else-branch(false) both declare pattern variable");
            requireDisjoint(condB.whenFalse, thenB.whenTrue,
                "cond(false) and then-branch(true) both declare pattern variable");
            requireDisjoint(condB.whenFalse, thenB.whenFalse,
                "cond(false) and then-branch(false) both declare pattern variable");
            requireDisjoint(thenB.whenTrue, elseB.whenTrue,
                "then-branch(true) and else-branch(true) both declare pattern variable");
            requireDisjoint(thenB.whenFalse, elseB.whenFalse,
                "then-branch(false) and else-branch(false) both declare pattern variable");


            // No rule for introducing bindings from a ? b : c itself, in either
            // direction: it can't be known at compile time whether a is true.
            return Bindings.empty();
        } else if (e instanceof ParenthesizedExpression p) {
            // §6.3.1.7 — (a): pass through unchanged.
            return analyze(p.getExpressionAt(0));

        }
        return Bindings.empty();
    }

    private static Map<LocationVariable, Expression> union(Map<LocationVariable, Expression> a,
            Map<LocationVariable, Expression> b) {
        var result = new LinkedHashMap<>(a);
        result.putAll(b);
        return result;
    }

    private static void requireDisjoint(Map<LocationVariable, Expression> a,
            Map<LocationVariable, Expression> b, String message) {
        for (LocationVariable name : a.keySet()) {
            if (b.containsKey(name)) {
                throw new IllegalStateException(message + ": '" + name + "'");
            }
        }
    }
}
