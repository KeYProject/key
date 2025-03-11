/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.operator.adt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Represents a function giving the length of a sequence.
 *
 * @author bruns
 * @since 1.7.2120
 *
 */
public class SeqLength extends Operator {

    public SeqLength(ExtList children) {
        super(children);
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
        return Operator.PREFIX;
    }

}
