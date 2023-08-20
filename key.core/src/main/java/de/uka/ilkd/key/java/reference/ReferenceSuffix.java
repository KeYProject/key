/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.reference;

import de.uka.ilkd.key.java.ModelElement;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Reference;
import de.uka.ilkd.key.java.SourceElement;

/**
 * Reference suffix. There are only few pure suffices, e.g. {@link SuperConstructorReference}. This
 * interface does not extend {@link Reference}, as
 * {@link recoder.java.expression.ParenthesizedExpression} is a qualifier but not a reference per
 * se.
 */

public interface ReferenceSuffix extends ModelElement, ProgramElement, SourceElement {

    /**
     * @return the prefix in the access path, or null if there is none.
     */
    // ReferencePrefix getReferencePrefix();
}
