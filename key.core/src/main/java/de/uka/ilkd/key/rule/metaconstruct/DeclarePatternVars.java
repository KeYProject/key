/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.java.visitor.BindingVariableVisitor;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableList;

/**
 * The meta construct {@code #declarePatternVars}: expands an expression into the declarations of
 * every pattern variable occurring in it.
 *
 * <p>
 * The declarations are deliberately bare ({@code T x;}, without an initializer). A guard that
 * binds pattern variables is compiled into nested {@code if}s in which each variable is assigned
 * exactly on the paths where its pattern matched. Declaring the variables before the guard makes
 * them available after the guard, where JLS 6.3.1.2 allows the continuation to refer to them.
 *
 * <p>
 * The variables of all polarities are declared, because a compound guard can use variables bound
 * when it is true as well as variables bound when it is false. Record components are included;
 * their values are assigned by {@link RecordPatternTest}.
 *
 * @author Alexander Weigl
 */
@TransformerMeta(name = "#declarePatternVars")
public final class DeclarePatternVars extends ProgramTransformer {

    /**
     * @param body the schema variable holding the guard expression
     */
    public DeclarePatternVars(ProgramElement body) {
        super("#declarePatternVars", body);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        var sv = (SchemaVariable) body();
        var expression = (Expression) svInst.getInstantiation(sv);
        return BindingVariableVisitor.allPatternVariables(expression).stream()
                .map(DeclarePatternVars::declaration)
                .toArray(ProgramElement[]::new);
    }

    private static Statement declaration(de.uka.ilkd.key.logic.op.LocationVariable variable) {
        var type = new TypeRef(variable.getKeYJavaType());
        return new LocalVariableDeclaration(type,
            new VariableSpecification(variable, variable.getKeYJavaType()));
    }

    @Override
    public ImmutableList<ProgramElement> getArguments() {
        return ImmutableList.of(body());
    }
}
