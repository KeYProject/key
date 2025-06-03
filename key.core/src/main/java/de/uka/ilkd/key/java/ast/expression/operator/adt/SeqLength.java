/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator.adt;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Represents a function giving the length of a sequence.
 *
 * @author bruns
 * @since 1.7.2120
 *
 */
public class SeqLength extends Operator {


    public SeqLength(PositionInfo pi, List<Comment> c, Expression child) {
        super(pi, c, new ImmutableArray<>(Objects.requireNonNull(child)));
    }

    public SeqLength(ExtList changeList) {
        super(changeList);
    }


    @Override
    public int getPrecedence() {
        return 0;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnSeqLength(this);
    }


    @Override
    public int getArity() {
        return 1;
    }


    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
    }


    @Override
    public int getNotation() {
        return PREFIX;
    }

}
