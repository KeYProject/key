/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import recoder.ModelException;
import recoder.java.Expression;

/**
 * Exception indicating that a particular type rule has been violated.
 *
 * @author AL
 */
public class TypingException extends ModelException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -1396794920221995373L;
    private final Expression expression;

    /**
     * Constructor without explanation text.
     *
     * @param expr the expression that could not be typed.
     */
    public TypingException(Expression expr) {
        expression = expr;
    }

    /**
     * Constructor with an explanation text.
     *
     * @param s an explanation.
     * @param expr the expression that could not be typed.
     */
    public TypingException(String s, Expression expr) {
        super(s);
        expression = expr;
    }

    /**
     * Returns the expression that could not be typed.
     */
    public Expression getUntypableExpression() {
        return expression;
    }
}
