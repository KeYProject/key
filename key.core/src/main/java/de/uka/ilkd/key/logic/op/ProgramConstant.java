/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.expression.literal.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This class represents currently only static final fields initialised with a compile time
 * constant. These fields cannot occur on the left side of an update.
 */
@NullMarked
public final class ProgramConstant extends ProgramVariable {

    // the value of the initializer as a literal, if this variable is
    // a compile-time constant, <code>null</code> otherwise
    private final @Nullable Literal compileTimeConstant;

    public ProgramConstant(ProgramElementName name, KeYJavaType t,
            @Nullable KeYJavaType containingType,
            boolean isStatic, @Nullable Literal compileTimeConstant) {
        super(name, t.getSort(), t, containingType, isStatic, false, false);
        this.compileTimeConstant = compileTimeConstant;
    }


    /**
     * @return the value of the initializer as a literal, if this variable is a compile-time
     *         constant, </code>null</code> otherwise
     */
    public @Nullable Literal getCompileTimeConstant() {
        return compileTimeConstant;
    }


    @Override
    public void visit(Visitor v) {
        v.performActionOnProgramConstant(this);
    }
}
