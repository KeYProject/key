/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;


public class AllFields extends ADTPrefixConstruct {

    /**
     *
     */
    private static final long serialVersionUID = 3940415948467563540L;


    public AllFields(Expression lhs) {
        super(lhs);
        makeParentRoleValid();
    }


    protected AllFields(AllFields proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public AllFields deepClone() {
        return new AllFields(this);
    }


    @Override
    public int getArity() {
        return 1;
    }


    @Override
    public int getNotation() {
        return PREFIX;
    }

}
