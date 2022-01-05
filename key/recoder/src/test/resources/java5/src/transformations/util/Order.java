// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

/**
 * This interface defines two order relation between objects. The <CODE>
 * lessOrEquals</CODE> predicate defines an order, the <CODE>less</CODE>
 * predicate defines a strict order. Both orders may be partial. The following
 * must hold:
 * <UL>
 * <LI>the orders are <I>antisymmetric </I> and <I>asymmetric </I> (strict
 * order) <BR>
 * <CODE>lessOrEquals(x,&nbsp;y)&nbsp;&amp;&amp;&nbsp;lessOrEquals(y,&nbsp;x)
 * </CODE> implies <CODE>equals(x,&nbsp;y)</CODE> and <CODE>less(x,&nbsp;y)
 * </CODE> implies <CODE>!less(y,&nbsp;x)</CODE></LI>
 * <LI>the orders are <I>reflexive </I> and <I>irreflexive </I> (strict order)
 * <BR>
 * <CODE>lessOrEquals(x,&nbsp;x)</CODE> and <CODE>!less(x,&nbsp;x)</CODE>
 * </LI>
 * <LI>the orders are <I>transitive </I> <BR>
 * <CODE>(less(x,&nbsp;y)&nbsp;&amp;&amp;&nbsp;less(y,&nbsp;z))</CODE> implies
 * <CODE>less(x,&nbsp;z)</CODE> (same for <CODE>lessOrEquals</CODE>).</LI>
 * <LI>the orders can be <I>total </I>( <I>alternative </I>, <I>linear </I>)
 * <BR>
 * <CODE>isComparable(x,&nbsp;y)</CODE> implies <CODE>
 * less(x,&nbsp;y)&nbsp;||&nbsp;less(y,&nbsp;x)</CODE></LI>
 * </UL>
 * As both relations are related by <BLOCKQUOTE><CODE>
 * lessOrEquals(x,&nbsp;y)&nbsp;==&nbsp;(less(x,&nbsp;y)&nbsp;||&nbsp;equals(x,&nbsp;y))
 * </CODE>, </BLOCKQUOTE> this interface extends an equality relation.
 * <P>
 * <SMALL>The usual way is to calculate all relations at once and returning a
 * status code such as <CODE>int compareTo(x, y)</CODE>. However, this
 * function alone can not capture partial orders and is not efficient if the
 * single comparisons become costly - see for instance the subset relation. The
 * prize to pay for the more explicite interface is a slight code overhead, but
 * this should not lead to a noticeable loss of performance. And of course,
 * <CODE>lessOrEquals(x,&nbsp;y)</CODE> should be a bit more comprehensible
 * than <CODE>compareTo(x,&nbsp;y)&nbsp; <=&nbsp;0</CODE>. </SMALL>
 * <P>
 * Whether or not objects of different type or <CODE>null</CODE> objects are
 * allowed is up to the specific implementation. This <CODE>isComparable
 * </CODE> predicate should be defined for all objects. The orders are total, if
 * the predicate yields true for any input - with the possible exception of
 * <CODE>null</CODE> objects. If two objects are not comparable, the result of
 * the other predicates is not defined unless stated explicitely.
 * 
 * @author AL
 */
public interface Order extends Equality {

    /**
     * Check if both objects can be related.
     * 
     * @param x
     *            the first object.
     * @param y
     *            the second object.
     * @return true if both objects can be compared, false otherwise.
     */
    boolean isComparable(Object x, Object y);

    /**
     * Check if the first object is less than the second one. This comparison is
     * strict: <CODE>less(x,&nbsp;y)</CODE> implies <CODE>!equals(x,&nbsp;y)
     * </CODE>.
     * 
     * @param x
     *            the first object.
     * @param y
     *            the second object.
     * @return true if the first object is less than the second one.
     */
    boolean less(Object x, Object y);

    /**
     * Check if the first object is greater than the second one. This comparison
     * is strict: <CODE>greater(x,&nbsp;y)</CODE> implies <CODE>
     * !equals(x,&nbsp;y)</CODE>.
     * 
     * @param x
     *            the first object.
     * @param y
     *            the second object.
     * @return true if the first object is greater than the second one.
     */
    boolean greater(Object x, Object y);

    /**
     * Check if the first object is less than or equals the second one.
     * 
     * @param x
     *            the first object.
     * @param y
     *            the second object.
     * @return true if the first object is less than or equals the second one.
     */
    boolean lessOrEquals(Object x, Object y);

    /**
     * Check if the first object is greater than or equals the second one.
     * 
     * @param x
     *            the first object.
     * @param y
     *            the second object.
     * @return true if the first object is greater than or equals the second
     *         one.
     */
    boolean greaterOrEquals(Object x, Object y);

    /**
     * Natural order implementation using the inherited default methods. This
     * implementation operates on the standard hash codes and implements
     * {@link recoder.util.HashCode}, which will work for Integer but might be
     * pretty meaningless for other types. No <CODE>null</CODE> objects are
     * allowed, but all others are comparable.
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
     * Natural order relation object based on the objects' natural hash codes.
     * The order is total except for <CODE>null</CODE> objects.
     */
    Order NATURAL = new Order.Natural();

    /**
     * Identity order implementation comparing objects by address. The
     * implementation uses <CODE>System.identityHashCode</CODE> and implements
     * {@link recoder.util.HashCode}. The order is based upon this encoding
     * which allows retrieval of objects but has no further meaning. Note that
     * <CODE>x&nbsp;!=&nbsp;null</CODE> implies <CODE>less(null,&nbsp;x)
     * </CODE> and of course <CODE>equals(null,&nbsp;null)</CODE>.
     */
    class Identity implements Order, HashCode {
        public final boolean equals(Object x, Object y) {
            return x == y;
        }

        public final int hashCode(Object x) {
            return System.identityHashCode(x);
        }

        public final boolean isComparable(Object x, Object y) {
            return true;
        }

        public final boolean less(Object x, Object y) {
            return System.identityHashCode(x) < System.identityHashCode(x);
        }

        public final boolean greater(Object x, Object y) {
            return System.identityHashCode(x) > System.identityHashCode(x);
        }

        public final boolean lessOrEquals(Object x, Object y) {
            return System.identityHashCode(x) <= System.identityHashCode(x);
        }

        public final boolean greaterOrEquals(Object x, Object y) {
            return System.identityHashCode(x) >= System.identityHashCode(x);
        }
    }

    /**
     * Identity order relation object based on the objects' identities. The
     * order is total, including <CODE>null</CODE> objects (which are minimum
     * elements).
     */
    Order IDENTITY = new Order.Identity();

    /**
     * Custom lexical order implementation comparing objects by comparison of a
     * unicode string mapping.
     */
    abstract class CustomLexicalOrder implements Order, HashCode {

        // null objects are forbidded or may result in empty Strings
        protected abstract String toString(Object x);

        public final int hashCode(Object x) {
            return toString(x).hashCode();
        }

        public boolean isComparable(Object x, Object y) {
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
     * Lexical order implementation comparing objects by their unicode string
     * representations.
     */
    class Lexical extends CustomLexicalOrder {

        protected String toString(Object x) {
            return x.toString();
        }

        public final boolean isComparable(Object x, Object y) {
            return x != null && y != null;
        }
    }

    /**
     * Lexical order relation object based on the objects' textual
     * representation. The order is total except for <CODE>null</CODE>
     * objects.
     */
    Order LEXICAL = new Order.Lexical();

}

