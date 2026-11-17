/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.operator.TypeCast;
import de.uka.ilkd.key.java.ast.statement.JmlAssert;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement;
import de.uka.ilkd.key.speclang.jml.translation.ProgramVariableCollection;
import de.uka.ilkd.key.speclang.njml.JmlFacade;
import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableList;

/**
 * The meta construct {@code #assumeBinding}: assumes the equality between a pattern variable and
 * the value it was bound to.
 *
 * <p>
 * The assignment {@code T x = (T) subject;} already evaluates the subject once; the equality
 * {@code x == subject} is a proof hint that lets the prover transfer the type and non-null
 * information from the tested subject to the pattern variable. It is emitted on the branch where
 * the pattern matched, so it is not an assumption about an unmatched variable.
 *
 * @author Alexander Weigl
 */
@TransformerMeta(name = "#assumeBinding")
public final class AssumeBinding extends ProgramTransformer {
    private final SchemaVariable variable;
    private final SchemaVariable value;

    /**
     * @param variable the pattern variable that was assigned
     * @param value the tested subject (or the component value) that was assigned
     */
    public AssumeBinding(ProgramElement variable, ProgramElement value) {
        super("#assumeBinding", variable);
        this.variable = (SchemaVariable) variable;
        this.value = (SchemaVariable) value;
    }

    @Override
    public ImmutableList<ProgramElement> getArguments() {
        return ImmutableList.of((ProgramElement) variable, (ProgramElement) value);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        var var = (ProgramVariable) svInst.getInstantiation(variable);
        var expression = (Expression) svInst.getInstantiation(value);
        var assumption = assumption(var, expression, services);
        return assumption == null ? new ProgramElement[0] : new ProgramElement[] { assumption };
    }

    /**
     * Builds the assume statement {@code variable == value}. Returns {@code null} if the value
     * cannot be converted to a logic term (for example because it needs a method-frame context).
     */
    static Statement assumption(ProgramVariable variable, Expression value, Services services) {
        return assumption(variable, value, true, services);
    }

    /**
     * Like {@link #assumption(ProgramVariable, Expression, Services)}, but optionally also assumes
     * that the variable is non-null. A type pattern only matches a non-null value; an any pattern
     * also matches null, so the caller must choose.
     */
    static Statement assumption(ProgramVariable variable, Expression value, boolean nonNull,
            Services services) {
        var unwrapped = value instanceof TypeCast cast ? cast.getExpressionAt(0) : value;
        final JTerm valueTerm;
        try {
            valueTerm = services.getTypeConverter().convertToLogicElement(unwrapped, null);
        } catch (RuntimeException e) {
            return null;
        }
        var termBuilder = services.getTermBuilder();
        JTerm equality = termBuilder.equals(valueTerm, termBuilder.var(variable));
        if (nonNull && !(variable.getKeYJavaType().getJavaType() instanceof PrimitiveType)) {
            JTerm nonNullTerm = termBuilder
                    .not(termBuilder.equals(termBuilder.var(variable), termBuilder.NULL()));
            equality = termBuilder.and(equality, nonNullTerm);
        }

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
}
