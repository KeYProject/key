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

import org.key_project.util.collection.ImmutableList;

/**
 * The meta construct {@code #patternTest}: expands the record patterns contained in an expression
 * into the equivalent plain boolean expressions.
 *
 * <p>
 * A record pattern matches more than {@code value instanceof Record}: every component pattern has
 * to match the corresponding component value, and a component value has to be read through the
 * record's accessor method (JLS 14.30.2). This meta construct produces exactly those tests so that
 * the program calculus can evaluate the guard. Type patterns are left unchanged; they are
 * decomposed by the pattern-aware assignment rules.
 *
 * @see de.uka.ilkd.key.rule.metaconstruct.PositiveBindingsOfExpr
 */
@TransformerMeta(name = "#patternTest")
public final class PatternTest extends ProgramTransformer {

    /**
     * @param body the schema variable holding the expression to rewrite
     */
    public PatternTest(ProgramElement body) {
        super("#patternTest", body);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        if (pe instanceof Expression expression) {
            return new ProgramElement[] { BindingVariableVisitor.toTest(expression) };
        }
        return new ProgramElement[] { pe };
    }

    @Override
    public ImmutableList<ProgramElement> getArguments() {
        return ImmutableList.of(body());
    }
}
