/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import recoder.java.Expression;
import recoder.java.expression.ParenthesizedExpression;


public class PassiveExpression extends ParenthesizedExpression {


    /**
     *
     */
    private static final long serialVersionUID = 4916068787633267648L;

    /**
     * creates a newly generated passive expression
     */
    public PassiveExpression() {
        super();
    }

    /**
     * creates a newly generated passive expression
     */
    public PassiveExpression(Expression e) {
        super(e);
    }

    public PassiveExpression(PassiveExpression proto) {
        super(proto);
    }

    public PassiveExpression deepClone() {
        return new PassiveExpression(this);
    }
}
