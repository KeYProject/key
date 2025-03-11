/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;


public class SeqIndexOf extends Operator {

    private static final long serialVersionUID = -6353396950660375581L;


    /**
     * Creates an "index of" operator.
     *
     * @param seq Sequence to operate on
     * @param elem The element to look for in the sequence
     */
    public SeqIndexOf(Expression seq, Expression elem) {
        super(seq, elem);
        makeParentRoleValid();
    }


    protected SeqIndexOf(SeqIndexOf proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public SeqIndexOf deepClone() {
        return new SeqIndexOf(this);
    }


    @Override
    public int getArity() {
        return 2;
    }


    @Override
    public int getPrecedence() {
        return 0;
    }


    @Override
    public int getNotation() {
        return PREFIX;
    }


    @Override
    public void accept(SourceVisitor v) {

    }

    @Override
    public String toSource() {
        return "\\indexOf(" + children.get(0).toSource() + "," + children.get(1).toSource() + ")";
    }
}
