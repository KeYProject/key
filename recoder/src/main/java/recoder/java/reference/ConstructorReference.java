// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.reference;

import recoder.java.Expression;
import recoder.java.Statement;
import recoder.list.generic.ASTList;

/**
 * Constructor reference.
 *
 * @author <TT>AutoDoc</TT>
 */

public interface ConstructorReference extends MemberReference, Statement {

    /**
     * Get arguments.
     *
     * @return the expression mutable list.
     */
    ASTList<Expression> getArguments();

    /**
     * Set arguments.
     *
     * @param list an expression mutable list.
     */
    void setArguments(ASTList<Expression> list);
}
