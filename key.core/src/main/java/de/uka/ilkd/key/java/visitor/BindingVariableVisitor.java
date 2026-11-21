/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.visitor;

import java.util.*;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.ast.expression.operator.*;
import de.uka.ilkd.key.java.ast.pattern.AnyPattern;
import de.uka.ilkd.key.java.ast.pattern.Pattern;
import de.uka.ilkd.key.java.ast.pattern.RecordPattern;
import de.uka.ilkd.key.java.ast.pattern.RecordPatternComponent;
import de.uka.ilkd.key.java.ast.pattern.TypePattern;
import de.uka.ilkd.key.logic.op.LocationVariable;

/**
 * Computes the pattern variables that are definitely matched by a boolean expression when it
 * evaluates to {@code true} or to {@code false}, following JLS 6.3.1.
 *
 * <p>
 * The analysis is used for JML name resolution only. The prover does not use these bindings: a
 * pattern variable is assigned when the corresponding {@code instanceof} test is evaluated (see
 * the {@code instanceof_eval_*} rules and
 * {@link de.uka.ilkd.key.rule.metaconstruct.RecordPatternUnfold}).
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

    public static boolean binds(Expression e) {
        if (e instanceof InstanceofPattern) {
            // §6.3.1.5 — a instanceof p
            return true;
        } else if (e instanceof BinaryOperator bo) {
            if (bo.getKind() == BinaryOperatorKind.LOGICAL_AND
                    || bo.getKind() == BinaryOperatorKind.LOGICAL_OR) {
                // §6.3.1.1/2 — a && b, a || b
                return binds(bo.getExpressionAt(0)) || binds(bo.getExpressionAt(1));
            }
        } else if (e instanceof UnaryOperator not && not.kind == UnaryOperatorKind.LOGICAL_NOT) {
            // §6.3.1.3 — !a: true/false swap.
            return binds(not.getExpressionAt(0));
        } else if (e instanceof Conditional c) {
            // §6.3.1.4 — a ? b : c
            return binds(c.getExpressionAt(0)) || binds(c.getExpressionAt(1))
                    || binds(c.getExpressionAt(2));
        } else if (e instanceof ParenthesizedExpression p) {
            // §6.3.1.7 — (a): pass through unchanged.
            return binds(p.getExpressionAt(0));
        }
        return false;
    }

    public static Bindings analyze(Expression e) {
        if (e instanceof InstanceofPattern io) {
            // §6.3.1.5 — a instanceof p
            // "when true" = variables declared by p. No "when false" rule:
            // it can't be determined at compile time that the match failed
            // in a way that still binds anything.
            Map<LocationVariable, Expression> whenTrue = new LinkedHashMap<>();
            collectBindings(io.getPattern(), io.getExpressionAt(0), whenTrue);
            return new Bindings(whenTrue, Map.of());
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

    private static Expression methodCall(Expression receiver, RecordPatternComponent component) {
        return KeYJavaASTFactory.methodCall(
            (de.uka.ilkd.key.java.ast.reference.ReferencePrefix) receiver,
            component.getAccessorName().getProgramName());
    }

    private static void collectBindings(Pattern pattern, Expression subject,
            Map<LocationVariable, Expression> bindings) {
        if (pattern instanceof TypePattern typePattern) {
            bindings.put(variable(typePattern.getVariable()),
                new TypeCast(subject, typePattern.getTypeReference()));
        } else if (pattern instanceof AnyPattern anyPattern) {
            if (anyPattern.getVariable() != null) {
                // The value is converted implicitly: the component type is a subtype of (or equal
                // to) the declared pattern type, so no cast is needed.
                bindings.put(variable(anyPattern.getVariable()), subject);
            }
        } else if (pattern instanceof RecordPattern recordPattern) {
            Expression receiver = new ParenthesizedExpression(
                new TypeCast(subject, recordPattern.getTypeReference()));
            for (RecordPatternComponent component : recordPattern.getComponents()) {
                collectBindings(component.getPattern(), methodCall(receiver, component), bindings);
            }
        }
    }

    private static LocationVariable variable(VariableSpecification specification) {
        return (LocationVariable) specification.getProgramVariable();
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
