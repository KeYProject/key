/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.literal;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.MapLDT;

import org.key_project.logic.Name;

import org.jspecify.annotations.Nullable;

public non-sealed class EmptyMapLiteral extends Literal {
    public static final EmptyMapLiteral INSTANCE = new EmptyMapLiteral(null, null);

    public EmptyMapLiteral(@Nullable PositionInfo pi, @Nullable List<Comment> comments) {
        super(pi, comments);
    }

    @Override
    public boolean equals(Object o) {
        return o == this;
    }

    @Override
    protected int computeHashCode() {
        return System.identityHashCode(this);
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnEmptyMapLiteral(this);
    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_MAP);
    }

    @Override
    public Name getLDTName() {
        return MapLDT.NAME;
    }

}