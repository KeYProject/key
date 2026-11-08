/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.Objects;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.util.collection.ImmutableList;

@TransformerMeta(name = "#lengthReference")
import org.jspecify.annotations.NullMarked;

@NullMarked
public class ArrayLength extends ProgramTransformer {

    /**
     * creates a typeof ProgramTransformer
     *
     * @param expr the instance of expression contained by the meta construct
     */
    public ArrayLength(Expression expr) {
        super("#lengthReference", expr);

    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations insts) {
        return new ProgramElement[] { KeYJavaASTFactory.fieldReference(services, "length",
            (Expression) pe, Objects.requireNonNull(insts.getExecutionContext(),
                "no execution context for array length")) };
    }

    @Override
    public ImmutableList<ProgramElement> getArguments() {
        return ImmutableList.of(body());
    }
}
