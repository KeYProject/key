/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.ast.expression.operator.Instanceof;
import de.uka.ilkd.key.java.ast.expression.operator.InstanceofPattern;
import de.uka.ilkd.key.java.ast.expression.operator.TypeCast;
import de.uka.ilkd.key.java.ast.pattern.AnyPattern;
import de.uka.ilkd.key.java.ast.pattern.Pattern;
import de.uka.ilkd.key.java.ast.pattern.RecordPattern;
import de.uka.ilkd.key.java.ast.pattern.RecordPatternComponent;
import de.uka.ilkd.key.java.ast.pattern.TypePattern;
import de.uka.ilkd.key.java.ast.reference.ReferencePrefix;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableList;

/**
 * The meta construct {@code #unfoldRecordPattern}: lowers one record-pattern test into plain Java
 * statements.
 *
 * <p>
 * For {@code #v = subject instanceof R(p1, ..., pn)} it generates
 *
 * <pre>
 * RType tmp = subject;          // the subject is evaluated exactly once
 * #v = false;
 * if (tmp instanceof R) {
 *     C1 c1 = ((R) tmp).a1();   // accessor invoked once, in component order
 *     ...tests and bindings for p1...
 *     Cn cn = ((R) tmp).an();
 *     ...tests and bindings for pn...
 *     #v = true;
 * }
 * </pre>
 *
 * <p>
 * A component pattern that is not a match-all pattern guards the remaining components, so a
 * failing component stops the match and the later accessors are not invoked (JLS 14.30.2). A
 * match-all pattern matches every value, including {@code null}, and only binds its variable.
 *
 * <p>
 * The accessor of a record component can complete abruptly. JLS 14.30.2 then requires the pattern
 * match to throw a {@code MatchException}. That is not modelled yet, so the converter rejects
 * record patterns over records with an explicit accessor; for the generated (implicit) accessors a
 * plain call is equivalent.
 *
 * <p>
 * The pattern variables are declared where they are bound. The branch that consumes them is
 * evaluated after the guard, and the program variables keep the value assigned here.
 *
 * @author Alexander Weigl
 */
@TransformerMeta(name = "#unfoldRecordPattern")
public final class RecordPatternUnfold extends ProgramTransformer {
    private final SchemaVariable resultVariable;
    private final SchemaVariable expression;

    /**
     * @param resultVariable the boolean variable that receives the result of the pattern match
     * @param expression the expression {@code subject instanceof RecordPattern}
     */
    public RecordPatternUnfold(ProgramElement resultVariable, ProgramElement expression) {
        super("#unfoldRecordPattern", resultVariable);
        this.resultVariable = (SchemaVariable) resultVariable;
        this.expression = (SchemaVariable) expression;
    }

    @Override
    public ImmutableList<ProgramElement> getArguments() {
        return ImmutableList.of((ProgramElement) resultVariable, (ProgramElement) expression);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        var result = (ProgramVariable) svInst.getInstantiation(resultVariable);
        var test = unwrap((Expression) svInst.getInstantiation(expression));
        if (!(test instanceof InstanceofPattern pattern)
                || !(pattern.getPattern() instanceof RecordPattern recordPattern)) {
            throw new IllegalStateException(
                "#unfoldRecordPattern expects a record pattern, but got " + test);
        }

        requireImplicitAccessors(recordPattern);

        Expression subject = pattern.getExpressionAt(0);
        TypeReference subjectType = new TypeRef(subject.getKeYJavaType(services, null));
        LocationVariable subjectTemp = fresh("subj", subjectType, services);

        List<Statement> statements = new ArrayList<>();
        statements.add(KeYJavaASTFactory.declare(subjectTemp, subject, subjectType));
        statements.add(KeYJavaASTFactory.assign(result, KeYJavaASTFactory.falseLiteral()));
        statements.add(KeYJavaASTFactory.ifThen(
            new Instanceof(subjectTemp, recordPattern.getTypeReference()),
            KeYJavaASTFactory.block(components(recordPattern, subjectTemp,
                List.of(KeYJavaASTFactory.assign(result, KeYJavaASTFactory.trueLiteral())),
                services))));
        return statements.toArray(ProgramElement[]::new);
    }

    /**
     * Compiles the component patterns of a record pattern. The statements in {@code after} run
     * only if every component pattern matches.
     */
    private List<Statement> components(RecordPattern pattern, Expression subject,
            List<Statement> after, Services services) {
        return components(pattern, 0, subject, after, services);
    }

    private List<Statement> components(RecordPattern pattern, int index, Expression subject,
            List<Statement> after, Services services) {
        if (index == pattern.getComponents().size()) {
            return after;
        }

        RecordPatternComponent component = pattern.getComponents().get(index);
        TypeReference componentType = componentType(component, services);
        LocationVariable value = fresh("c", componentType, services);

        Expression receiver = new ParenthesizedExpression(
            new TypeCast(subject, pattern.getTypeReference()));
        Expression accessor = KeYJavaASTFactory.methodCall((ReferencePrefix) receiver,
            component.getAccessorName().getProgramName());

        List<Statement> rest = components(pattern, index + 1, subject, after, services);
        List<Statement> result = new ArrayList<>();
        result.add(KeYJavaASTFactory.declare(value, accessor, componentType));

        Pattern componentPattern = component.getPattern();
        if (componentPattern instanceof AnyPattern anyPattern) {
            if (anyPattern.getVariable() != null) {
                result.add(KeYJavaASTFactory.assign(
                    (ProgramVariable) anyPattern.getVariable().getProgramVariable(), value));
            }
            result.addAll(rest);
        } else if (componentPattern instanceof TypePattern typePattern) {
            // leave the type test to the ordinary pattern rules: emitting an instanceof pattern
            // here gives the component binding exactly the same semantics (and the same
            // non-null/type information) as a top-level pattern variable
            result.add(KeYJavaASTFactory.ifThen(
                new InstanceofPattern(value, typePattern.getTypeReference(), typePattern),
                KeYJavaASTFactory.block(rest)));
        } else if (componentPattern instanceof RecordPattern nested) {
            result.add(KeYJavaASTFactory.ifThen(
                new Instanceof(value, nested.getTypeReference()),
                KeYJavaASTFactory.block(components(nested, 0, value, rest, services))));
        } else {
            throw new IllegalStateException("Unsupported component pattern: " + componentPattern);
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

    private static TypeReference componentType(RecordPatternComponent component,
            Services services) {
        if (component.getComponentType() != null) {
            return component.getComponentType();
        }
        Pattern pattern = component.getPattern();
        if (pattern instanceof RecordPattern recordPattern) {
            return recordPattern.getTypeReference();
        }
        if (pattern instanceof AnyPattern anyPattern) {
            if (anyPattern.getVariable() != null) {
                var variable = anyPattern.getVariable().getProgramVariable();
                if (variable.getKeYJavaType() != null) {
                    return new TypeRef(variable.getKeYJavaType());
                }
            }
        }
        // a conditional type pattern may test against a subtype of the component's declared type;
        // java.lang.Object is always a valid temporary type for the accessor result
        return new TypeRef(services.getJavaInfo().getKeYJavaType("java.lang.Object"));
    }

    private static LocationVariable fresh(String base, TypeReference type, Services services) {
        return new LocationVariable(new ProgramElementName(
            services.getTermBuilder().newName(base)), type);
    }

    private static Expression unwrap(Expression expression) {
        Expression result = expression;
        while (result instanceof ParenthesizedExpression parenthesized) {
            result = parenthesized.getExpressionAt(0);
        }
        return result;
    }
}
