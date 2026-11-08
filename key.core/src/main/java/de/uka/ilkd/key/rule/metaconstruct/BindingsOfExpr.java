/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.BindingVariableVisitor;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.op.sv.SchemaVariable;

/**
 * Expands an expression into the declarations of the pattern variables that are definitely bound if
 * the expression evaluates to {@code true}.
 * <p>
 * This is implemented by the two meta constructs {@code #posBinding} and {@code #negBinding}.
 * Given a guard expression such as {@code obj instanceof String s}, {@code #posBinding} produces
 * the statement {@code String s = (String) obj;}, i.e. the declarations analysed by
 * {@link BindingVariableVisitor#analyze(Expression)} in
 * {@link BindingVariableVisitor.Bindings#whenTrue()}, while {@code #negBinding} produces the
 * bindings that hold when the expression evaluates to {@code false}.
 *
 * @author Alexander Weigl
 */
public abstract class BindingsOfExpr extends ProgramTransformer {
    public final boolean positive;

    /**
     * @param positive whether this transformer produces the bindings asserted when the guard
     *        evaluates to {@code true} ({@code #posBinding}) or to {@code false}
     *        ({@code #negBinding})
     */
    protected BindingsOfExpr(String name, ProgramElement body, boolean positive) {
        super(name, body);
        assert body instanceof SchemaVariable;
        this.positive = positive;
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        var sv = (SchemaVariable) super.body();
        var e = (Expression) svInst.getInstantiation(sv);
        var bindings = BindingVariableVisitor.analyze(e);
        return BindingVariableVisitor.toStatements(
            positive ? bindings.whenTrue() : bindings.whenFalse());
    }
}
