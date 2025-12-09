/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.mset;

import de.uka.ilkd.key.java.recoderext.adt.ADTPrefixConstruct;

import recoder.java.Expression;

public class MSetMul extends ADTPrefixConstruct {

    /**
     *
     */
    private static final long serialVersionUID = -521447886220796576L;


    public MSetMul(Expression mset, Expression msetEl) {
        super(mset, msetEl);
        makeParentRoleValid();
    }


    protected MSetMul(de.uka.ilkd.key.java.recoderext.mset.MSetMul proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public de.uka.ilkd.key.java.recoderext.mset.MSetMul deepClone() {

        return new de.uka.ilkd.key.java.recoderext.mset.MSetMul(this);
    }


    @Override
    public int getArity() {
        return 2;
    }


    @Override
    public int getNotation() {
        return POSTFIX;
    }

    @Override
    public String toSource() {
        return children.get(0).toSource() + "[" + children.get(1).toSource() + "]";
    }
}
