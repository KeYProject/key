/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder;

import recoder.util.Order;

/**
 * A model element that carries a name.
 */
public interface NamedModelElement extends ModelElement {

    /**
     * Lexical order objects comparing names.
     */
    Order LEXICAL_ORDER = new LexicalOrder();

    /**
     * Return the name of the model element.
     *
     * @return the name of the model element.
     */
    String getName();

    /**
     * Lexical order on names of named model elements. The model elements may be null; null elements
     * are considered as empty strings.
     */
    class LexicalOrder extends Order.CustomLexicalOrder {

        protected String toString(Object x) {
            return (x == null) ? "" : ((NamedModelElement) x).getName();
        }

        public boolean isComparable(Object x, Object y) {
            return (x == null && y == null)
                    || ((x instanceof NamedModelElement) && (y instanceof NamedModelElement));
        }
    }

}
