/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.MapLDT;

import org.key_project.logic.Name;

import org.jspecify.annotations.NonNull;

public class EmptyMapLiteral extends Literal {

    public static final EmptyMapLiteral INSTANCE = new EmptyMapLiteral();

    private EmptyMapLiteral() {
    }

    @Override
    public boolean equals(@org.jspecify.annotations.Nullable Object o) {
        return o == this;
    }

    @Override
    protected int computeHashCode() {
        return System.identityHashCode(this);
    }

    @Override
    public void visit(@NonNull Visitor v) {
        v.performActionOnEmptyMapLiteral(this);
    }

    @Override
    public @NonNull KeYJavaType getKeYJavaType(@NonNull Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_MAP);
    }

    @Override
    public @NonNull Name getLDTName() {
        return MapLDT.NAME;
    }

}
