// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.reference;

import recoder.java.NonTerminalProgramElement;
import recoder.java.Reference;

/**
 * Reference suffix. There are only few pure suffices, e.g.
 * {@link SuperConstructorReference}. This interface does not extend
 * {@link Reference}, as
 * {@link recoder.java.expression.ParenthesizedExpression}is a qualifier but
 * not a reference per se.
 */

public interface ReferenceSuffix extends NonTerminalProgramElement {

    /**
     * @return the prefix in the access path, or null if there is none.
     */
    ReferencePrefix getReferencePrefix();
}