/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.ast.expression.operator.BinaryOperator;
import de.uka.ilkd.key.java.ast.expression.operator.Conditional;
import de.uka.ilkd.key.java.ast.expression.operator.InstanceofPattern;
import de.uka.ilkd.key.java.ast.expression.operator.UnaryOperator;
import de.uka.ilkd.key.java.ast.expression.operator.UnaryOperatorKind;
import de.uka.ilkd.key.java.ast.pattern.AnyPattern;
import de.uka.ilkd.key.java.ast.pattern.Pattern;
import de.uka.ilkd.key.java.ast.pattern.RecordPattern;
import de.uka.ilkd.key.java.ast.pattern.RecordPatternComponent;
import de.uka.ilkd.key.java.ast.pattern.TypePattern;
import de.uka.ilkd.key.java.ast.statement.JmlAssert;
import de.uka.ilkd.key.java.visitor.BindingVariableVisitor;
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
 * Internal assumptions that make the facts of a successful pattern match available to the prover.
 *
 * <p>
 * A pattern variable of a conditional type pattern is bound only if the value is an instance of the
 * pattern type, hence it is not {@code null}. The prover does not keep this fact across the guard
 * evaluation; a method call or field access on the pattern variable would otherwise have to prove
 * {@code x != null} from scratch. The assumption is emitted in the branch in which the variable is
 * in scope, so it is always true.
 *
 * <p>
 * Match-all patterns are deliberately excluded: they also match {@code null}.
 *
 * @author Alexander Weigl
 */
final class PatternBindingAssumptions {
    private PatternBindingAssumptions() {
    }

    static ProgramElement[] nonNull(Expression guard, boolean positive, Services services) {
        var bindings = BindingVariableVisitor.analyze(guard);
        Map<LocationVariable, Expression> inScope =
            positive ? bindings.whenTrue() : bindings.whenFalse();
        Set<LocationVariable> nonNullPatterns = new LinkedHashSet<>();
        collectTypePatternVariables(guard, nonNullPatterns);

        List<ProgramElement> result = new ArrayList<>();
        for (LocationVariable variable : inScope.keySet()) {
            if (nonNullPatterns.contains(variable)) {
                result.add(assumeNonNull(variable, services));
            }
        }
        return result.toArray(ProgramElement[]::new);
    }

    private static void collectTypePatternVariables(Expression expression,
            Set<LocationVariable> result) {
        if (expression instanceof InstanceofPattern pattern) {
            collectTypePatternVariables(pattern.getPattern(), result);
        } else if (expression instanceof BinaryOperator operator) {
            collectTypePatternVariables(operator.getExpressionAt(0), result);
            collectTypePatternVariables(operator.getExpressionAt(1), result);
        } else if (expression instanceof UnaryOperator not
                && not.kind == UnaryOperatorKind.LOGICAL_NOT) {
            collectTypePatternVariables(not.getExpressionAt(0), result);
        } else if (expression instanceof Conditional conditional) {
            collectTypePatternVariables(conditional.getExpressionAt(0), result);
            collectTypePatternVariables(conditional.getExpressionAt(1), result);
            collectTypePatternVariables(conditional.getExpressionAt(2), result);
        } else if (expression instanceof ParenthesizedExpression parenthesized) {
            collectTypePatternVariables(parenthesized.getExpressionAt(0), result);
        }
    }

    private static void collectTypePatternVariables(Pattern pattern,
            Set<LocationVariable> result) {
        if (pattern instanceof TypePattern typePattern) {
            result.add((LocationVariable) typePattern.getVariable().getProgramVariable());
        } else if (pattern instanceof RecordPattern recordPattern) {
            for (RecordPatternComponent component : recordPattern.getComponents()) {
                collectTypePatternVariables(component.getPattern(), result);
            }
        } else if (pattern instanceof AnyPattern) {
            // an any pattern matches null as well; no non-nullness follows
        }
    }

    private static JmlAssert assumeNonNull(LocationVariable variable, Services services) {
        var termBuilder = services.getTermBuilder();
        JTerm nonNull =
            termBuilder.not(termBuilder.equals(termBuilder.var(variable), termBuilder.NULL()));

        var condition = (JmlParser.ExpressionContext) JmlFacade.parseExpr("true");
        var construct = new TextualJMLAssertStatement(TextualJMLAssertStatement.Kind.ASSUME,
            new KeyAst.Expression(condition));
        var assumption = new JmlAssert(TextualJMLAssertStatement.Kind.ASSUME, construct, null);
        var variables = new ProgramVariableCollection(null, ImmutableList.nil(), null, null,
            Map.of(), Map.of(), Map.of(), Map.of());
        services.getSpecificationRepository().addStatementSpec(assumption,
            new SpecificationRepository.JmlStatementSpec(variables, ImmutableList.of(nonNull)));
        return assumption;
    }
}
