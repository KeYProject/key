/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.MSetLDT;

import org.key_project.logic.Name;

public class EmptyMSetLiteral extends Literal {

    public static final EmptyMSetLiteral INSTANCE = new EmptyMSetLiteral();

    private EmptyMSetLiteral() {}

    @Override
    public boolean equals(Object o) {
        return o == this;
    }

    @Override
    protected int computeHashCode() {
        return System.identityHashCode(this);
    }

    public void visit(Visitor v) {
        v.performActionOnEmptyMSetLiteral(this);
    }


    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_MSET);
    }

    @Override
    public Name getLDTName() {
        return MSetLDT.NAME;
    }
}
