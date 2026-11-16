/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.ast.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.ast.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.ast.expression.operator.BinaryOperatorKind;
import de.uka.ilkd.key.java.ast.expression.operator.Conditional;
import de.uka.ilkd.key.java.ast.expression.operator.Instanceof;
import de.uka.ilkd.key.java.ast.expression.operator.InstanceofPattern;
import de.uka.ilkd.key.java.ast.expression.operator.TypeCast;
import de.uka.ilkd.key.java.ast.expression.operator.UnaryOperator;
import de.uka.ilkd.key.java.ast.expression.operator.UnaryOperatorKind;
import de.uka.ilkd.key.java.ast.pattern.AnyPattern;
import de.uka.ilkd.key.java.ast.pattern.Pattern;
import de.uka.ilkd.key.java.ast.pattern.RecordPattern;
import de.uka.ilkd.key.java.ast.pattern.RecordPatternComponent;
import de.uka.ilkd.key.java.ast.pattern.TypePattern;
import de.uka.ilkd.key.java.ast.reference.ReferencePrefix;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.ast.statement.JmlAssert;
import de.uka.ilkd.key.java.visitor.BindingVariableVisitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement;
import de.uka.ilkd.key.speclang.jml.translation.ProgramVariableCollection;
import de.uka.ilkd.key.speclang.njml.JmlFacade;
import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.util.collection.ImmutableList;

/**
 * Compiles a boolean expression that contains {@code instanceof} patterns into nested Java
 * statements.
 *
 * <p>
 * The expression is not evaluated into a single boolean first. Instead, every pattern test is
 * compiled into an {@code if} whose then branch contains the pattern variable's declaration and the
 * continuation:
 *
 * <pre>
 * a instanceof T b &amp;&amp; b.test()
 * </pre>
 *
 * becomes
 *
 * <pre>
 * { T0 t = a;
 *   if (t instanceof T) {
 *       T b = (T) t;
 *       if (b.test()) { onTrue } else { onFalse }
 *   } else { onFalse }
 * }
 * </pre>
 *
 * <p>
 * This places every pattern variable in the lexical scope where JLS 6.3.1 allows it and preserves
 * short-circuit evaluation: the subject of a later operand is only evaluated inside the branch of
 * the earlier operand.
 *
 * <p>
 * A no-else {@code if} has no branch for the continuation after the {@code if}. For this case the
 * compiler has already created, for every pattern variable, a boolean "matched" flag and a value
 * temporary. The flag and value are assigned when the pattern matches; after the compiled block
 * the pattern variable is declared in the continuation as
 *
 * <pre>
 * T b = matched ? (T) value : default;
 * </pre>
 *
 * The cast is only executed on the path where the pattern matched. If the then branch can complete
 * normally, the continuation cannot legally read {@code b} (JLS 6.3.1.2), so no "always aborts"
 * analysis is needed.
 *
 * @author Alexander Weigl
 */
final class PatternLowering {
    private PatternLowering() {
    }

    /**
     * A value and a match flag for a pattern variable, used to introduce the variable after an
     * {@code if} whose then branch is the only alternative to the pattern match.
     */
    private static final class Capture {
        final LocationVariable matched;
        final LocationVariable value;
        final TypeReference type;
        final boolean nonNull;

        Capture(LocationVariable matched, LocationVariable value, TypeReference type,
                boolean nonNull) {
            this.matched = matched;
            this.value = value;
            this.type = type;
            this.nonNull = nonNull;
        }
    }

    static ProgramElementList rewriteIf(Expression guard, Statement thenBranch,
            Statement elseBranch, Services services) {
        boolean hasElse = elseBranch != null;
        Map<LocationVariable, Capture> captures = new LinkedHashMap<>();
        List<Statement> result = new ArrayList<>();
        if (!hasElse) {
            collectPatternVariables(guard, captures, services);
            for (Capture capture : captures.values()) {
                result.add(KeYJavaASTFactory.declare(capture.matched,
                    KeYJavaASTFactory.falseLiteral(),
                    new TypeRef(services.getJavaInfo().getKeYJavaType("boolean"))));
                result.add(KeYJavaASTFactory.declare(capture.value, defaultValue(capture.type),
                    capture.type));
            }
        }

        List<Statement> onTrue = new ArrayList<>();
        onTrue.add(thenBranch);
        List<Statement> onFalse = new ArrayList<>();
        if (elseBranch != null) {
            onFalse.add(elseBranch);
        }

        List<Statement> compiled = compile(guard, onTrue, onFalse, captures, services);
        result.add(KeYJavaASTFactory.block(compiled));

        if (!hasElse) {
            Map<LocationVariable, Expression> after = BindingVariableVisitor.analyze(guard)
                    .whenFalse();
            for (LocationVariable variable : after.keySet()) {
                Capture capture = captures.get(variable);
                if (capture != null) {
                    result.add(declareFromCapture(variable, capture, services));
                    if (capture.nonNull) {
                        result.add(KeYJavaASTFactory.ifThen(capture.matched,
                            block(List.of(assumeEquality(variable, capture.value, services)))));
                    }
                }
            }
        }
        return new ProgramElementList(result);
    }

    private static List<Statement> compile(Expression expression, List<Statement> onTrue,
            List<Statement> onFalse, Map<LocationVariable, Capture> captures, Services services) {
        if (expression instanceof ParenthesizedExpression parenthesized) {
            return compile(parenthesized.getExpressionAt(0), onTrue, onFalse, captures, services);
        }
        if (expression instanceof InstanceofPattern pattern) {
            return compilePattern(pattern, onTrue, onFalse, captures, services);
        }
        if (expression instanceof BinaryOperator operator) {
            if (operator.getKind() == BinaryOperatorKind.LOGICAL_AND) {
                List<Statement> right =
                    compile(operator.getExpressionAt(1), onTrue, onFalse, captures, services);
                return compile(operator.getExpressionAt(0), right, onFalse, captures, services);
            }
            if (operator.getKind() == BinaryOperatorKind.LOGICAL_OR) {
                List<Statement> right =
                    compile(operator.getExpressionAt(1), onTrue, onFalse, captures, services);
                return compile(operator.getExpressionAt(0), onTrue, right, captures, services);
            }
        }
        if (expression instanceof UnaryOperator not && not.kind == UnaryOperatorKind.LOGICAL_NOT) {
            return compile(not.getExpressionAt(0), onFalse, onTrue, captures, services);
        }
        if (expression instanceof Conditional conditional) {
            List<Statement> thenBranch = compile(conditional.getExpressionAt(1), onTrue, onFalse,
                captures, services);
            List<Statement> elseBranch = compile(conditional.getExpressionAt(2), onTrue, onFalse,
                captures, services);
            return compile(conditional.getExpressionAt(0), thenBranch, elseBranch, captures,
                services);
        }
        // a boolean subexpression without patterns is evaluated exactly once by the if
        return List.of(KeYJavaASTFactory.ifElse(expression, block(onTrue), block(onFalse)));
    }

    private static List<Statement> compilePattern(InstanceofPattern pattern,
            List<Statement> onTrue, List<Statement> onFalse,
            Map<LocationVariable, Capture> captures, Services services) {
        Expression subject = pattern.getExpressionAt(0);
        TypeReference subjectType;
        try {
            subjectType = new TypeRef(subject.getKeYJavaType(services, null));
        } catch (RuntimeException e) {
            // a method call needs an execution context here; Object is a valid supertype
            subjectType = new TypeRef(services.getJavaInfo().getKeYJavaType("java.lang.Object"));
        }
        LocationVariable subjectTemp = fresh("t", subjectType, services);
        List<Statement> result = new ArrayList<>();
        result.add(KeYJavaASTFactory.declare(subjectTemp, subject, subjectType));

        if (pattern.getPattern() instanceof TypePattern typePattern) {
            List<Statement> body = new ArrayList<>();
            LocationVariable variable =
                (LocationVariable) typePattern.getVariable().getProgramVariable();
            body.add(KeYJavaASTFactory.declare(variable,
                new TypeCast(subjectTemp, typePattern.getTypeReference()),
                typePattern.getTypeReference()));
            body.add(assumeEquality(variable, subjectTemp, services));
            body.addAll(capture(variable, subjectTemp, true, captures));
            body.addAll(onTrue);
            result.add(KeYJavaASTFactory.ifElse(
                new Instanceof(subjectTemp, typePattern.getTypeReference()), block(body),
                block(onFalse)));
        } else if (pattern.getPattern() instanceof RecordPattern recordPattern) {
            requireImplicitAccessors(recordPattern);
            List<Statement> body = components(recordPattern, subjectTemp, 0, onTrue, onFalse,
                captures, services);
            result.add(KeYJavaASTFactory.ifElse(
                new Instanceof(subjectTemp, recordPattern.getTypeReference()), block(body),
                block(onFalse)));
        } else {
            throw new IllegalStateException("Unsupported pattern: " + pattern.getPattern());
        }
        return result;
    }

    private static void requireImplicitAccessors(RecordPattern pattern) {
        for (RecordPatternComponent component : pattern.getComponents()) {
            if (!component.hasImplicitAccessor()) {
                throw new IllegalStateException(
                    "Record patterns over records with an explicit accessor are not supported "
                        + "yet: JLS 14.30.2 requires wrapping accessor failures in MatchException "
                        + "(component '" + component.getAccessorName() + "')");
            }
            if (component.getPattern() instanceof RecordPattern nested) {
                requireImplicitAccessors(nested);
            }
        }
    }

    private static List<Statement> components(RecordPattern pattern, Expression subject, int index,
            List<Statement> onTrue, List<Statement> onFalse,
            Map<LocationVariable, Capture> captures, Services services) {
        if (index == pattern.getComponents().size()) {
            return onTrue;
        }
        RecordPatternComponent component = pattern.getComponents().get(index);
        TypeReference componentType = componentType(component, services);
        LocationVariable value = fresh("c", componentType, services);
        Expression receiver = new ParenthesizedExpression(
            new TypeCast(subject, pattern.getTypeReference()));
        Expression accessor = KeYJavaASTFactory.methodCall((ReferencePrefix) receiver,
            component.getAccessorName().getProgramName());

        List<Statement> rest = components(pattern, subject, index + 1, onTrue, onFalse, captures,
            services);
        List<Statement> result = new ArrayList<>();
        result.add(KeYJavaASTFactory.declare(value, accessor, componentType));

        Pattern componentPattern = component.getPattern();
        if (componentPattern instanceof AnyPattern anyPattern) {
            if (anyPattern.getVariable() != null) {
                LocationVariable variable =
                    (LocationVariable) anyPattern.getVariable().getProgramVariable();
                result.add(KeYJavaASTFactory.declare(variable, value,
                    new TypeRef(variable.getKeYJavaType())));
                result.addAll(capture(variable, value, false, captures));
            }
            result.addAll(rest);
        } else if (componentPattern instanceof TypePattern typePattern) {
            LocationVariable variable =
                (LocationVariable) typePattern.getVariable().getProgramVariable();
            List<Statement> body = new ArrayList<>();
            body.add(KeYJavaASTFactory.declare(variable,
                new TypeCast(value, typePattern.getTypeReference()),
                typePattern.getTypeReference()));
            body.add(assumeEquality(variable, value, services));
            body.addAll(capture(variable, value, true, captures));
            body.addAll(rest);
            result.add(KeYJavaASTFactory.ifElse(
                new Instanceof(value, typePattern.getTypeReference()), block(body),
                block(onFalse)));
        } else if (componentPattern instanceof RecordPattern nested) {
            result.add(KeYJavaASTFactory.ifElse(
                new Instanceof(value, nested.getTypeReference()),
                block(components(nested, value, 0, rest, onFalse, captures, services)),
                block(onFalse)));
        } else {
            throw new IllegalStateException("Unsupported component pattern: " + componentPattern);
        }
        return result;
    }

    private static List<Statement> capture(LocationVariable variable, Expression value,
            boolean cast, Map<LocationVariable, Capture> captures) {
        Capture capture = captures.get(variable);
        if (capture == null) {
            return List.of();
        }
        Expression assignedValue = cast
                ? new TypeCast(value, new TypeRef(variable.getKeYJavaType()))
                : value;
        return List.of(
            KeYJavaASTFactory.assign(capture.matched, KeYJavaASTFactory.trueLiteral()),
            KeYJavaASTFactory.assign(capture.value, assignedValue));
    }

    private static Statement declareFromCapture(LocationVariable variable, Capture capture,
            Services services) {
        Expression then = new TypeCast(capture.value, new TypeRef(variable.getKeYJavaType()));
        Expression condition = new Conditional(PositionInfo.UNDEFINED, List.of(),
            capture.matched, then, defaultValue(new TypeRef(variable.getKeYJavaType())));
        return KeYJavaASTFactory.declare(variable, condition,
            new TypeRef(variable.getKeYJavaType()));
    }

    private static void collectPatternVariables(Expression expression,
            Map<LocationVariable, Capture> captures, Services services) {
        if (expression instanceof ParenthesizedExpression parenthesized) {
            collectPatternVariables(parenthesized.getExpressionAt(0), captures, services);
        } else if (expression instanceof InstanceofPattern pattern) {
            collectPatternVariables(pattern.getPattern(), captures, services);
        } else if (expression instanceof BinaryOperator operator) {
            collectPatternVariables(operator.getExpressionAt(0), captures, services);
            collectPatternVariables(operator.getExpressionAt(1), captures, services);
        } else if (expression instanceof UnaryOperator not
                && not.kind == UnaryOperatorKind.LOGICAL_NOT) {
            collectPatternVariables(not.getExpressionAt(0), captures, services);
        } else if (expression instanceof Conditional conditional) {
            collectPatternVariables(conditional.getExpressionAt(0), captures, services);
            collectPatternVariables(conditional.getExpressionAt(1), captures, services);
            collectPatternVariables(conditional.getExpressionAt(2), captures, services);
        }
    }

    private static void collectPatternVariables(Pattern pattern,
            Map<LocationVariable, Capture> captures, Services services) {
        if (pattern instanceof TypePattern typePattern) {
            addCapture((LocationVariable) typePattern.getVariable().getProgramVariable(), captures,
                services, true);
        } else if (pattern instanceof AnyPattern anyPattern) {
            if (anyPattern.getVariable() != null) {
                addCapture((LocationVariable) anyPattern.getVariable().getProgramVariable(),
                    captures, services, false);
            }
        } else if (pattern instanceof RecordPattern recordPattern) {
            for (RecordPatternComponent component : recordPattern.getComponents()) {
                collectPatternVariables(component.getPattern(), captures, services);
            }
        }
    }

    private static void addCapture(LocationVariable variable,
            Map<LocationVariable, Capture> captures, Services services, boolean nonNull) {
        if (captures.containsKey(variable)) {
            return;
        }
        var type = new TypeRef(variable.getKeYJavaType());
        captures.put(variable, new Capture(
            fresh("m", new TypeRef(services.getJavaInfo().getKeYJavaType("boolean")), services),
            fresh("v", type, services), type, nonNull));
    }

    private static TypeReference componentType(RecordPatternComponent component,
            Services services) {
        if (component.getComponentType() != null) {
            return component.getComponentType();
        }
        Pattern pattern = component.getPattern();
        if (pattern instanceof RecordPattern recordPattern) {
            return recordPattern.getTypeReference();
        }
        if (pattern instanceof AnyPattern anyPattern && anyPattern.getVariable() != null) {
            var variable = anyPattern.getVariable().getProgramVariable();
            if (variable.getKeYJavaType() != null) {
                return new TypeRef(variable.getKeYJavaType());
            }
        }
        return new TypeRef(services.getJavaInfo().getKeYJavaType("java.lang.Object"));
    }

    private static Statement assumeEquality(LocationVariable variable, Expression value,
            Services services) {
        var termBuilder = services.getTermBuilder();
        final JTerm valueTerm = services.getTypeConverter().convertToLogicElement(value, null);
        JTerm equality = termBuilder.equals(valueTerm, termBuilder.var(variable));

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

    private static Expression defaultValue(TypeReference type) {
        var javaType = type.getKeYJavaType().getJavaType();
        if (javaType instanceof PrimitiveType primitive) {
            return primitive.getDefaultValue();
        }
        return NullLiteral.NULL;
    }

    private static LocationVariable fresh(String base, TypeReference type, Services services) {
        return new LocationVariable(
            new ProgramElementName(services.getTermBuilder().newName(base)), type);
    }

    private static de.uka.ilkd.key.java.ast.StatementBlock block(List<Statement> statements) {
        return KeYJavaASTFactory.block(statements);
    }

    /** The result of a rewriting; a small list wrapper for the metaconstruct API. */
    static final class ProgramElementList {
        final List<Statement> statements;

        ProgramElementList(List<Statement> statements) {
            this.statements = statements;
        }
    }
}
