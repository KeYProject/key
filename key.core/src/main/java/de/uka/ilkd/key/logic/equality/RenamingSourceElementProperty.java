/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.visitor.JavaASTTreeWalker;

/**
 * A property that can be used in
 * {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])} for
 * {@link SourceElement}s.
 */
public class RenamingSourceElementProperty implements Property<SourceElement> {
    /**
     * The single instance of this property.
     */
    public static final RenamingSourceElementProperty RENAMING_SOURCE_ELEMENT_PROPERTY =
        new RenamingSourceElementProperty();

    /**
     * This constructor is private as a single instance of this class should be shared. The instance
     * can be accessed
     * through {@link RenamingSourceElementProperty#RENAMING_SOURCE_ELEMENT_PROPERTY} and is used as
     * a parameter for
     * {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])}.
     */
    private RenamingSourceElementProperty() {}

    /**
     * Checks if {@code se2} is a source element syntactically equal to {@code se1} modulo renaming.
     *
     * @param se1 the first element of the equality check
     * @param se2 the second element of the equality check
     * @param v the additional arguments needed for the equality check
     * @return {@code true} iff {@code se2} is a source element syntactically equal to {@code se1}
     *         modulo renaming
     * @param <V> the type of the additional parameters needed for the comparison
     */
    @Override
    public <V> boolean equalsModThisProperty(SourceElement se1, SourceElement se2, V... v) {
        // For this equality check, v must be a single NameAbstractionTable
        NameAbstractionTable nat = (NameAbstractionTable) v[0];

        JavaASTTreeWalker tw1 = new JavaASTTreeWalker(se1);
        JavaASTTreeWalker tw2 = new JavaASTTreeWalker(se2);

        SourceElement next1 = tw1.getCurrentNode();
        SourceElement next2 = tw2.getCurrentNode();

        while (next1 != null && next2 != null) {
            if (!next1.equals(next2)) {
                return false;
            }
            next1 = tw1.nextNode();
            next2 = tw2.nextNode();
        }

        return next1 == null && next2 == null;
    }

    @Override
    public int hashCodeModThisProperty(SourceElement sourceElement) {
        return 0;
    }

    private boolean comparison(SourceElement se1, SourceElement se2) {
        return se1.equals(se2);
    }

    private boolean comparison(Comment comment, SourceElement se) {
        return true;
    }
}
