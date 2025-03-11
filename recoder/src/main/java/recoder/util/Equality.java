/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.util;

/**
 * This interface defines an equality relation between two objects. Equality relations are
 * <UL>
 * <LI><I>reflexive </I> <BR>
 * <CODE>equals(x, x)</CODE></LI>
 * <LI><I>symmetric </I> <BR>
 * {@code  equals(x, y) == equals(y, x)}</LI>
 * <LI><I>transitive </I> <BR>
 * {@code (equals(x, y) && equals(y, z))} implies
 * {@code  equals(x, z)}</LI>
 * </UL>
 * Whether objects of different type or <CODE>null</CODE> objects are allowed is up to the
 * specific implementation.
 *
 * @author AL
 */
public interface Equality {

    /**
     * Natural equality relation object. The implementation calls {@code x.equals(y)}, hence no
     * <CODE>null</CODE> are allowed (not even for y, as the relation must be symmetric).
     */
    Equality NATURAL = Order.NATURAL;
    /**
     * Identity equality relation object. The implementation compares x and y for object identity
     * (x == y). Two <CODE>null</CODE> objects are considered equal.
     */
    Equality IDENTITY = Order.IDENTITY;

    /**
     * Compares two objects for equality.
     *
     * @param x the first object.
     * @param y the second object.
     * @return true, if x equals y, false otherwise.
     */
    boolean equals(Object x, Object y);
}
