/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.java.recoderext.adt;

import recoder.java.Expression;


public class Intersect extends ADTPrefixConstruct {

    /**
     *
     */
    private static final long serialVersionUID = 8777658515734186914L;


    public Intersect(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }


    protected Intersect(Intersect proto) {
        super(proto);
        makeParentRoleValid();
    }


    @Override
    public Intersect deepClone() {
        return new Intersect(this);
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
}
