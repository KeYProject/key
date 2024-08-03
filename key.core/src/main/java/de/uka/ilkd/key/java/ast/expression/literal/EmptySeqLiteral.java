/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.literal;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.SeqLDT;

import org.key_project.logic.Name;



public non-sealed class EmptySeqLiteral extends Literal {

    public static final EmptySeqLiteral INSTANCE = new EmptySeqLiteral();

    private EmptySeqLiteral() {}

    @Override
    public boolean equals(Object o) {
        return o == this;
    }

    @Override
    protected int computeHashCode() {
        return System.identityHashCode(this);
    }

    public void visit(Visitor v) {
        v.performActionOnEmptySeqLiteral(this);
    }


    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_SEQ);
    }

    @Override
    public Name getLDTName() {
        return SeqLDT.NAME;
    }
}
