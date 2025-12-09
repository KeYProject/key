/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.mset;

import de.uka.ilkd.key.java.recoderext.adt.ADTPrefixConstruct;

import recoder.java.Expression;

public class MSetIntersect extends ADTPrefixConstruct {

    /**
     *
     */
    private static final long serialVersionUID = 8877658515734186914L;


    public MSetIntersect(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }


    protected MSetIntersect(de.uka.ilkd.key.java.recoderext.mset.MSetIntersect proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public de.uka.ilkd.key.java.recoderext.mset.MSetIntersect deepClone() {
        return new de.uka.ilkd.key.java.recoderext.mset.MSetIntersect(this);
    }


    @Override
    public int getArity() {
        return 2;
    }


    @Override
    public int getNotation() {
        return PREFIX;
    }
}
