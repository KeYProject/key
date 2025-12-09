/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.mset;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class MSetCard extends Operator {


    private static final long serialVersionUID = 0;


    public MSetCard(Expression msetEl) {
        super(msetEl);
        makeParentRoleValid();
    }


    protected MSetCard(de.uka.ilkd.key.java.recoderext.mset.MSetCard proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public de.uka.ilkd.key.java.recoderext.mset.MSetCard deepClone() {
        return new de.uka.ilkd.key.java.recoderext.mset.MSetCard(this);
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
