/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.reference;

import de.uka.ilkd.key.java.ast.ModelElement;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.Reference;
import de.uka.ilkd.key.java.ast.SourceElement;

/**
 * Reference suffix. There are only few pure suffices, e.g. {@link SuperConstructorReference}. This
 * interface does not extend {@link Reference}, as ParenthesizedExpression is a qualifier but not a
 * reference per
 * se.
 */

public interface ReferenceSuffix extends ModelElement, ProgramElement, SourceElement {

    /**
     * @return the prefix in the access path, or null if there is none.
     */
    // ReferencePrefix getReferencePrefix();
}
