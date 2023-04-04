// This file is part of the RECODER library and protected by the LGPL.

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
