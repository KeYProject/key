/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext.mset;

import de.uka.ilkd.key.java.recoderext.adt.ADTPrefixConstruct;
import de.uka.ilkd.key.java.recoderext.adt.SeqSingleton;

import recoder.java.Expression;

public class MSetSingle extends ADTPrefixConstruct {

    /**
     *
     */
    private static final long serialVersionUID = 970102046205262465L;

    public MSetSingle(Expression lhs) {
        super(lhs);
        makeParentRoleValid();
    }


    protected MSetSingle(SeqSingleton proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public MSetSingle deepClone() {
        return new MSetSingle(this);
    }


    @Override
    public int getArity() {
        return 1;
    }


    @Override
    public int getNotation() {
        return PREFIX;
    }

    @Override
    public String toSource() {
        return "\\mset_single(" + children.get(0) + ")";
    }
}
