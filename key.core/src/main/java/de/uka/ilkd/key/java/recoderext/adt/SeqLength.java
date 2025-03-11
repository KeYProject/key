/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * @since 1.7.2118
 * @author bruns
 *
 */
public class SeqLength extends Operator {

    private static final long serialVersionUID = 0;


    public SeqLength(Expression seq) {
        super(seq);
        makeParentRoleValid();
    }


    protected SeqLength(SeqLength proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public SeqLength deepClone() {
        return new SeqLength(this);
    }


    @Override
    public int getArity() {
        return 1;
    }


    @Override
    public int getPrecedence() {
        return 0;
    }


    @Override
    public int getNotation() {
        return POSTFIX;
    }


    @Override
    public void accept(SourceVisitor v) {

    }

    public String toSource() {
        return children.get(0).toSource() + ".length";
    }

}
