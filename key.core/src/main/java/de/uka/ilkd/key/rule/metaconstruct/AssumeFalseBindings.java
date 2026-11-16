/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableList;

/**
 * The meta construct {@code #assumeFalseBindings}: assumes the facts that hold for the pattern
 * variables introduced by the given guard when it evaluates to {@code false}.
 *
 * @see PatternBindingAssumptions
 */
@TransformerMeta(name = "#assumeFalseBindings")
public final class AssumeFalseBindings extends ProgramTransformer {
    public AssumeFalseBindings(ProgramElement body) {
        super("#assumeFalseBindings", body);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        var expression = (Expression) svInst.getInstantiation((SchemaVariable) body());
        return PatternBindingAssumptions.nonNull(expression, false, services);
    }

    @Override
    public ImmutableList<ProgramElement> getArguments() {
        return ImmutableList.of(body());
    }
}
