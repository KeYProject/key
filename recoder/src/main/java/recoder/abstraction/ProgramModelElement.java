/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.abstraction;

import recoder.NamedModelElement;
import recoder.bytecode.AccessFlags;
import recoder.convenience.Format;
import recoder.service.ProgramModelInfo;
import recoder.util.Order;

/**
 * An entity of the program meta model.
 *
 * @author AL
 * @author RN
 */
public interface ProgramModelElement extends NamedModelElement, AccessFlags {

    /**
     * Lexical order objects comparing full names. For partial names, use the corresponding order of
     * {@link recoder.NamedModelElement}.
     */
    Order LEXICAL_ORDER = new LexicalOrder();

    /**
     * Returns the maximal expanded name including all applicable qualifiers.
     *
     * @return the full name of this program model element.
     */
    String getFullName();

    /**
     * Returns the instance that can retrieve information about this program model element.
     *
     * @return the program model info of this element.
     */
    ProgramModelInfo getProgramModelInfo();

    /**
     * Sets the instance that can retrieve information about this program model element. Should not
     * be called from outside a service.
     *
     * @param pmi the program model info to be used for this element.
     */
    void setProgramModelInfo(ProgramModelInfo pmi);

    /**
     * Lexical order on full names of program model elements. For partial names, use the
     * corresponding order of {@link recoder.NamedModelElement}. Null elements are considered as
     * empty strings. Program elements are kept unambiguous by attaching source code file name and
     * positions.
     */
    class LexicalOrder implements Order {
        public final int hashCode(Object x) {
            if (x == null) {
                return 0;
            }
            String name = Format.toString("%N|%p|%u", (ProgramModelElement) x);
            if (name == null) {
                return 0;
            }
            return name.hashCode();
        }

        @SuppressWarnings("all")
        public final boolean isComparable(Object x, Object y) {
            return true;
        }

        private int diff(ProgramModelElement n1, ProgramModelElement n2) {
            if (n1 == n2) {
                return 0;
            }
            String s1 = (n1 == null) ? "" : Format.toString("%N", n1);
            String s2 = (n2 == null) ? "" : Format.toString("%N", n2);
            int res = diff(s1, s2);
            if (res == 0) {
                s1 = Format.toString("%p|%u", n1);
                s2 = Format.toString("%p|%u", n2);
                res = diff(s1, s2);
            }
            return res;
        }

        private int diff(String s1, String s2) {
            if (s1 == null) {
                s1 = "";
            }
            if (s2 == null) {
                s2 = "";
            }
            int len1 = s1.length();
            int len2 = s2.length();
            for (int i = 0, m = Math.min(len1, len2); i < m; i++) {
                char c1 = s1.charAt(i);
                char c2 = s2.charAt(i);
                if (c1 != c2) {
                    return c1 - c2;
                }
            }
            return len1 - len2;
        }

        public final boolean equals(Object x, Object y) {
            return diff((ProgramModelElement) x, (ProgramModelElement) y) == 0;
        }

        public final boolean less(Object x, Object y) {
            return diff((ProgramModelElement) x, (ProgramModelElement) y) < 0;
        }

        public final boolean greater(Object x, Object y) {
            return diff((ProgramModelElement) x, (ProgramModelElement) y) > 0;
        }

        public final boolean lessOrEquals(Object x, Object y) {
            return diff((ProgramModelElement) x, (ProgramModelElement) y) <= 0;
        }

        public final boolean greaterOrEquals(Object x, Object y) {
            return diff((ProgramModelElement) x, (ProgramModelElement) y) >= 0;
        }
    }
}
