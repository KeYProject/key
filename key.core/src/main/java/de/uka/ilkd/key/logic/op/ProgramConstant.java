/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;

/**
 * This class represents currently only static final fields initialised with a compile time
 * constant. These fields cannot occur on the left side of an update.
 */
public final class ProgramConstant extends ProgramVariable {

    // the value of the initializer as a literal, if this variable is
    // a compile-time constant, <code>null</code> otherwise
    private final Literal compileTimeConstant;

    public ProgramConstant(ProgramElementName name, KeYJavaType t, KeYJavaType containingType,
            boolean isStatic, Literal compileTimeConstant) {
        super(name, t.getSort(), t, containingType, isStatic, false, false);
        this.compileTimeConstant = compileTimeConstant;
    }


    /**
     * @return the value of the initializer as a literal, if this variable is a compile-time
     *         constant, </code>null</code> otherwise
     */
    public Literal getCompileTimeConstant() {
        return compileTimeConstant;
    }


    @Override
    public void visit(de.uka.ilkd.key.java.visitor.Visitor v) {
        v.performActionOnProgramConstant(this);
    }


    @Override
    public Operator rename(Name name) {
        return new ProgramConstant(new ProgramElementName(name.toString()), getKeYJavaType(),
            getContainerType(), isStatic(), compileTimeConstant);
    }
}
