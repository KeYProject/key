/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.util;

/**
 * This interface defines two order relation between objects. The <CODE>
 * lessOrEquals</CODE> predicate defines an order, the <CODE>less</CODE> predicate defines a strict
 * order. Both orders may be partial. The following must hold:
 * <UL>
 * <LI>the orders are <I>antisymmetric </I> and <I>asymmetric </I> (strict order) <BR>
 * <CODE>lessOrEquals(x,&nbsp;y)&nbsp;&amp;&amp;&nbsp;lessOrEquals(y,&nbsp;x)
 * </CODE> implies <CODE>equals(x,&nbsp;y)</CODE> and <CODE>less(x,&nbsp;y)
 * </CODE> implies <CODE>!less(y,&nbsp;x)</CODE></LI>
 * <LI>the orders are <I>reflexive </I> and <I>irreflexive </I> (strict order) <BR>
 * <CODE>lessOrEquals(x,&nbsp;x)</CODE> and <CODE>!less(x,&nbsp;x)</CODE></LI>
 * <LI>the orders are <I>transitive </I> <BR>
 * <CODE>(less(x,&nbsp;y)&nbsp;&amp;&amp;&nbsp;less(y,&nbsp;z))</CODE> implies
 * <CODE>less(x,&nbsp;z)</CODE> (same for <CODE>lessOrEquals</CODE>).</LI>
 * <LI>the orders can be <I>total </I>( <I>alternative </I>, <I>linear </I>) <BR>
 * <CODE>isComparable(x,&nbsp;y)</CODE> implies <CODE>
 * less(x,&nbsp;y)&nbsp;||&nbsp;less(y,&nbsp;x)</CODE></LI>
 * </UL>
 * As both relations are related by
 *
 * <pre>
 * {@code
 * lessOrEquals(x,y)==(less(x,y) || equals(x,y))}
 * ,
 * </pre>
 *
 * this interface extends an equality relation.
 * <p>
 * <SMALL>The usual way is to calculate all relations at once and returning a status code such as
 * <CODE>int compareTo(x, y)</CODE>. However, this function alone can not capture partial orders and
 * is not efficient if the single comparisons become costly - see for instance the subset relation.
 * The prize to pay for the more explicit interface is a slight code overhead, but this should not
 * lead to a noticeable loss of performance. And of course, {@code lessOrEquals(x,y)}
 * should be a bit more comprehensible than {@code compareTo(x,y) <= 0}.
 * </SMALL>
 * <p>
 * Whether objects of different type or {@code null} objects are allowed is up to the
 * specific implementation. This {@code isComparable}
 * predicate should be defined for all objects. The orders are total, if the predicate
 * yields true for any input - with the possible exception of {@code null} objects. If two
 * objects are not comparable, the result of the other predicates is not defined unless stated
 * explicitely.
 *
 * @author AL
 */
public interface Order extends Equality {

    /**
     * Natural order relation object based on the objects' natural hash codes. The order is total
     * except for <CODE>null</CODE> objects.
     */
    Order NATURAL = new Order.Natural();
    /**
     * Identity order relation object based on the objects' identities. The order is total,
     * including <CODE>null</CODE> objects (which are minimum elements).
     */
    Order IDENTITY = new Order.Identity();
    /**
     * Lexical order relation object based on the objects' textual representation. The order is
     * total except for <CODE>null</CODE> objects.
     */
    Order LEXICAL = new Order.Lexical();

    /**
     * Check if both objects can be related.
     *
     * @param x the first object.
     * @param y the second object.
     * @return true if both objects can be compared, false otherwise.
     */
    boolean isComparable(Object x, Object y);

    /**
     * Check if the first object is less than the second one. This comparison is strict:
     * <CODE>less(x,&nbsp;y)</CODE> implies <CODE>!equals(x,&nbsp;y)
     * </CODE>.
     *
     * @param x the first object.
     * @param y the second object.
     * @return true if the first object is less than the second one.
     */
    boolean less(Object x, Object y);

    /**
     * Check if the first object is greater than the second one. This comparison is strict:
     * <CODE>greater(x,&nbsp;y)</CODE> implies <CODE>
     * !equals(x,&nbsp;y)</CODE>.
     *
     * @param x the first object.
     * @param y the second object.
     * @return true if the first object is greater than the second one.
     */
    boolean greater(Object x, Object y);

    /**
     * Check if the first object is less than or equals the second one.
     *
     * @param x the first object.
     * @param y the second object.
     * @return true if the first object is less than or equals the second one.
     */
    boolean lessOrEquals(Object x, Object y);

    /**
     * Check if the first object is greater than or equals the second one.
     *
     * @param x the first object.
     * @param y the second object.
     * @return true if the first object is greater than or equals the second one.
     */
    boolean greaterOrEquals(Object x, Object y);

    /**
     * Natural order implementation using the inherited default methods. This implementation
     * operates on the standard hash codes and implements {@link recoder.util.HashCode}, which will
     * work for Integer but might be pretty meaningless for other types. No <CODE>null</CODE>
     * objects are allowed, but all others are comparable.
     */
    class Natural implements Order, HashCode {
        public final boolean equals(Object x, Object y) {
            return x.equals(y);
        }

        public final int hashCode(Object x) {
            return x.hashCode();
        }

        public final boolean isComparable(Object x, Object y) {
            return x != null && y != null;
        }

        public final boolean less(Object x, Object y) {
            return x.hashCode() < y.hashCode();
        }

        public final boolean greater(Object x, Object y) {
            return x.hashCode() > y.hashCode();
        }

        public final boolean lessOrEquals(Object x, Object y) {
            return x.hashCode() <= y.hashCode();
        }

        public final boolean greaterOrEquals(Object x, Object y) {
            return x.hashCode() >= y.hashCode();
        }
    }

    /**
     * Identity order implementation comparing objects by address. The implementation uses
     * <CODE>System.identityHashCode</CODE> and implements {@link recoder.util.HashCode}. The order
     * is based upon this encoding which allows retrieval of objects but has no further meaning.
     * Note that <CODE>x&nbsp;!=&nbsp;null</CODE> implies <CODE>less(null,&nbsp;x)
     * </CODE> and of course <CODE>equals(null,&nbsp;null)</CODE>.
     */
    class Identity implements Order, HashCode {
        public final boolean equals(Object x, Object y) {
            return x == y;
        }

        public final int hashCode(Object x) {
            return System.identityHashCode(x);
        }

        public final boolean isComparable(@SuppressWarnings("unused") Object x,
                @SuppressWarnings("unused") Object y) {
            return true;
        }

        /**
         * compares the given objects using there identity hash code
         *
         * @param x the first object.
         * @param y the second object.
         * @return true if the identity hash code of the first object is less than that of the
         *         second object
         */
        public final boolean less(Object x, Object y) {
            return System.identityHashCode(x) < System.identityHashCode(y);
        }

        /**
         * compares the given objects using there identity hash code
         *
         * @param x the first object.
         * @param y the second object.
         * @return true if the identity hash code of the first object is greater than that of the
         *         second object
         */
        public final boolean greater(Object x, Object y) {
            return System.identityHashCode(x) > System.identityHashCode(y);
        }

        /**
         * compares the given objects using there identity hash code
         *
         * @param x the first object.
         * @param y the second object.
         * @return true if the identity hash code of the first object is less or equal than
         *         that of the second object
         */
        public final boolean lessOrEquals(Object x, Object y) {
            return System.identityHashCode(x) <= System.identityHashCode(y);
        }

        /**
         * compares the given objects using there identity hash code
         *
         * @param x the first object.
         * @param y the second object.
         * @return true if the identity hash code of the first object is greater or equal than
         *         that of the second object
         */
        public final boolean greaterOrEquals(Object x, Object y) {
            return System.identityHashCode(x) >= System.identityHashCode(y);
        }
    }

    /**
     * Custom lexical order implementation comparing objects by comparison of a unicode string
     * mapping.
     */
    abstract class CustomLexicalOrder implements Order, HashCode {

        // null objects are forbidden or may result in empty Strings
        protected abstract String toString(Object x);

        public final int hashCode(Object x) {
            return toString(x).hashCode();
        }

        public boolean isComparable(@SuppressWarnings("unused") Object x,
                @SuppressWarnings("unused") Object y) {
            return true;
        }

        private int diff(Object x, Object y) {
            String s1 = toString(x);
            String s2 = toString(y);
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
            return diff(x, y) == 0;
        }

        public final boolean less(Object x, Object y) {
            return diff(x, y) < 0;
        }

        public final boolean greater(Object x, Object y) {
            return diff(x, y) > 0;
        }

        public final boolean lessOrEquals(Object x, Object y) {
            return diff(x, y) <= 0;
        }

        public final boolean greaterOrEquals(Object x, Object y) {
            return diff(x, y) >= 0;
        }
    }

    /**
     * Lexical order implementation comparing objects by their unicode string representations.
     */
    class Lexical extends CustomLexicalOrder {

        protected String toString(Object x) {
            return x.toString();
        }

        public final boolean isComparable(Object x, Object y) {
            return x != null && y != null;
        }
    }

}
