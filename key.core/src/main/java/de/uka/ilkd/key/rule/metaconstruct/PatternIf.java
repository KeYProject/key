/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableList;

/**
 * The meta construct {@code #patternIf}: lowers {@code if (guard) then} for a guard that contains
 * {@code instanceof} patterns.
 *
 * @see PatternLowering
 */
@TransformerMeta(name = "#patternIf")
public final class PatternIf extends ProgramTransformer {
    private final SchemaVariable guard;
    private final SchemaVariable then;

    public PatternIf(ProgramElement guard, ProgramElement then) {
        super("#patternIf", guard);
        this.guard = (SchemaVariable) guard;
        this.then = (SchemaVariable) then;
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        var expression = (Expression) svInst.getInstantiation(guard);
        var thenStatement = (Statement) svInst.getInstantiation(then);
        return PatternLowering.rewriteIf(expression, thenStatement, null, services).statements
                .toArray(ProgramElement[]::new);
    }

    @Override
    public ImmutableList<ProgramElement> getArguments() {
        return ImmutableList.of((ProgramElement) guard, (ProgramElement) then);
    }
}
