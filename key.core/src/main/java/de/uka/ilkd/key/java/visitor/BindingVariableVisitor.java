/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.visitor;

import java.util.*;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.ast.expression.operator.*;
import de.uka.ilkd.key.java.ast.pattern.AnyPattern;
import de.uka.ilkd.key.java.ast.pattern.Pattern;
import de.uka.ilkd.key.java.ast.pattern.RecordPattern;
import de.uka.ilkd.key.java.ast.pattern.RecordPatternComponent;
import de.uka.ilkd.key.java.ast.pattern.TypePattern;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.ast.statement.JmlAssert;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement;
import de.uka.ilkd.key.speclang.jml.translation.ProgramVariableCollection;
import de.uka.ilkd.key.speclang.njml.JmlFacade;
import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.util.collection.ImmutableList;

/**
 * Analyses the pattern variables declared by a binding expression and expands them into the local
 * variable declarations that are valid where the expression is known to have a given value,
 * following the flow-scoping rules of JLS 6.3.1.
 * <p>
 * The analysis handles {@code instanceof} patterns as well as {@code &&}, {@code ||}, {@code !},
 * the conditional operator and parentheses. Record patterns are destructured recursively: the
 * value of a component is read by invoking the record's accessor method, exactly as specified by
 * JLS 14.30.2.
 * <p>
 * The result is consumed by the pattern-aware taclets: {@code #posBinding} and
 * {@code #negBinding} turn the bindings into local-variable declarations (with the tested
 * expression cast to the pattern type), so that a pattern variable is usable exactly in those
 * branches in which the corresponding check has succeeded.
 *
 * @author Alexander Weigl
 */
public class BindingVariableVisitor {

    /**
     * The pattern variables that are guaranteed to be bound for the two outcomes of an
     * expression, each mapped to the expression the variable is bound to (a cast of the tested
     * expression).
     *
     * @param whenTrue the bindings that hold when the expression evaluates to {@code true}
     * @param whenFalse the bindings that hold when the expression evaluates to {@code false}
     */
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

    /**
     * Returns whether the given expression may bind pattern variables, i.e. whether it contains
     * an {@code instanceof} pattern below {@code &&}, {@code ||}, {@code !}, the conditional
     * operator or parentheses.
     *
     * @param e the expression to inspect
     * @return {@code true} if the expression contains an {@code instanceof} pattern
     */
    public static boolean binds(Expression e) {
        if (e instanceof InstanceofPattern) {
            // §6.3.1.5 — a instanceof p
            // "when true" = variables declared by p. No "when false" rule:
            // it can't be determined at compile time that the match failed
            // in a way that still binds anything.
            return true;
        } else if (e instanceof BinaryOperator bo) {
            if (bo.getKind() == BinaryOperatorKind.LOGICAL_AND) {
                // §6.3.1.1 — a && b
                return binds(bo.getExpressionAt(0)) || binds(bo.getExpressionAt(1));
            } else if (bo.getKind() == BinaryOperatorKind.LOGICAL_OR) {
                // §6.3.1.2 — a || b (mirror image of &&)
                return binds(bo.getExpressionAt(0)) || binds(bo.getExpressionAt(1));
            }
        } else if (e instanceof UnaryOperator not && not.kind == UnaryOperatorKind.LOGICAL_NOT) {
            // §6.3.1.3 — !a: true/false swap.
            return binds(not.getExpressionAt(0));
        } else if (e instanceof Conditional c) {
            // §6.3.1.4 — a ? b : c
            return binds(c.getExpressionAt(0))
                    || binds(c.getExpressionAt(1))
                    || binds(c.getExpressionAt(2));
        } else if (e instanceof ParenthesizedExpression p) {
            // §6.3.1.7 — (a): pass through unchanged.
            return binds(p.getExpressionAt(0));

        }
        return false;
    }


    /**
     * Computes the pattern variables that are guaranteed to be bound when the given expression
     * evaluates to {@code true} or to {@code false}, following JLS 6.3.1.1 to 6.3.1.7.
     * <p>
     * Bindings are only reported for the outcome in which they are guaranteed, so the result is
     * conservative: a binding that cannot be determined statically is omitted rather than
     * guessed.
     *
     * @param e the boolean expression to analyze
     * @return the bindings for the true and the false outcome of {@code e}
     */
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

    /**
     * Rewrites {@code e} so that it can be evaluated by the program calculus: the record patterns
     * contained in it are replaced by the equivalent plain boolean expressions.
     *
     * <p>
     * A record pattern cannot simply be erased to {@code e instanceof R}: a component type pattern
     * that is not unconditional does not match {@code null}, and nested record patterns need their
     * own tests (JLS 14.30.2). Type patterns are left untouched; they are decomposed by the
     * existing pattern rules.
     *
     * @param e the expression to rewrite
     * @return an expression equivalent to {@code e} that contains no record pattern
     */
    public static Expression toTest(Expression e) {
        if (e instanceof InstanceofPattern io && io.getPattern() instanceof RecordPattern rp) {
            List<Expression> tests = new ArrayList<>();
            Expression subject = io.getExpressionAt(0);
            tests.add(new Instanceof(subject, io.getTypeReference()));
            addComponentTests(rp, subject, tests);
            return conjunction(tests);
        } else if (e instanceof BinaryOperator bo
                && (bo.getKind() == BinaryOperatorKind.LOGICAL_AND
                        || bo.getKind() == BinaryOperatorKind.LOGICAL_OR)) {
            Expression left = toTest(bo.getExpressionAt(0));
            Expression right = toTest(bo.getExpressionAt(1));
            if (left == bo.getExpressionAt(0) && right == bo.getExpressionAt(1)) {
                return bo;
            }
            return new BinaryOperator(bo.getPositionInfo(), List.of(bo.getComments()), bo.getKind(),
                left, right);
        } else if (e instanceof UnaryOperator not && not.kind == UnaryOperatorKind.LOGICAL_NOT) {
            Expression child = toTest(not.getExpressionAt(0));
            if (child == not.getExpressionAt(0)) {
                return not;
            }
            return new UnaryOperator(not.getPositionInfo(), List.of(not.getComments()), not.kind,
                child);
        } else if (e instanceof Conditional cond) {
            Expression condition = toTest(cond.getExpressionAt(0));
            Expression thenBranch = toTest(cond.getExpressionAt(1));
            Expression elseBranch = toTest(cond.getExpressionAt(2));
            if (condition == cond.getExpressionAt(0) && thenBranch == cond.getExpressionAt(1)
                    && elseBranch == cond.getExpressionAt(2)) {
                return cond;
            }
            return new Conditional(cond.getPositionInfo(), List.of(cond.getComments()), condition,
                thenBranch, elseBranch);
        } else if (e instanceof ParenthesizedExpression p) {
            Expression child = toTest(p.getExpressionAt(0));
            if (child == p.getExpressionAt(0)) {
                return p;
            }
            return new ParenthesizedExpression(p.getPositionInfo(), List.of(p.getComments()),
                child);
        }
        return e;
    }

    /**
     * Adds the tests for the components of a record pattern.
     *
     * @param pattern the record pattern whose components are tested
     * @param subject the expression that is known to be an instance of the record type
     * @param tests the list the generated tests are appended to
     */
    private static void addComponentTests(RecordPattern pattern, Expression subject,
            List<Expression> tests) {
        Expression receiver =
            new ParenthesizedExpression(new TypeCast(subject, pattern.getTypeReference()));
        for (RecordPatternComponent component : pattern.getComponents()) {
            Expression value = methodCall(receiver, component);
            Pattern nested = component.getPattern();
            if (nested instanceof TypePattern typePattern) {
                tests.add(new Instanceof(value, typePattern.getTypeReference()));
            } else if (nested instanceof RecordPattern recordPattern) {
                tests.add(new Instanceof(value, recordPattern.getTypeReference()));
                addComponentTests(recordPattern, value, tests);
            }
            // An AnyPattern matches every value (including null): no test.
        }
    }

    private static Expression conjunction(List<Expression> tests) {
        Expression result = tests.get(0);
        for (int i = 1; i < tests.size(); i++) {
            result = KeYJavaASTFactory.logicalAndOperator(result, tests.get(i));
        }
        return result;
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

    /**
     * Turns a binding (a map from pattern variables to their cast expressions) into a sequence of
     * local variable declarations of the form {@code Type var = (Type) expr;}.
     * <p>
     * The declarations introduce the pattern variables of an {@code instanceof} pattern so that
     * they are usable in the branch of a conditional in which the analyzed expression is known to
     * evaluate to the corresponding truth value, see {@link #analyze(Expression)}.
     *
     * @param bindings a binding according to {@link Bindings#whenTrue()} or
     *        {@link Bindings#whenFalse()}
     * @param services the services used to convert the bound expression for the identity
     *        assumption
     * @return one fresh {@link LocalVariableDeclaration} per bound pattern variable, each
     *         followed by the assumption {@code expr == var} when it can be built
     */
    public static Statement[] toStatements(Map<LocationVariable, Expression> bindings,
            Services services) {
        var result = new ArrayList<Statement>();
        for (var entry : bindings.entrySet()) {
            var variable = entry.getKey();
            result.add(new LocalVariableDeclaration(
                new TypeRef(variable.getKeYJavaType()),
                new VariableSpecification(variable, entry.getValue(),
                    variable.getKeYJavaType())));
            var assumption = equalityAssumption(variable, entry.getValue(), services);
            if (assumption != null) {
                result.add(assumption);
            }
        }
        return result.toArray(Statement[]::new);
    }

    private static JmlAssert equalityAssumption(LocationVariable variable,
            Expression boundExpression,
            Services services) {
        var value = boundExpression instanceof TypeCast cast ? cast.getExpressionAt(0)
                : boundExpression;
        final JTerm valueTerm;
        try {
            valueTerm = services.getTypeConverter().convertToLogicElement(value, null);
        } catch (RuntimeException e) {
            return null;
        }
        var termBuilder = services.getTermBuilder();
        var equality = termBuilder.equals(valueTerm, termBuilder.var(variable));

        var condition = (JmlParser.ExpressionContext) JmlFacade.parseExpr("true");
        var construct = new TextualJMLAssertStatement(TextualJMLAssertStatement.Kind.ASSUME,
            new KeyAst.Expression(condition));
        var assumption = new JmlAssert(TextualJMLAssertStatement.Kind.ASSUME, construct, null);
        var variables = new ProgramVariableCollection(null, ImmutableList.nil(), null, null,
            Map.of(), Map.of(), Map.of(), Map.of());
        services.getSpecificationRepository().addStatementSpec(assumption,
            new SpecificationRepository.JmlStatementSpec(variables, ImmutableList.of(equality)));
        return assumption;
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
