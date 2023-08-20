/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;


import java.util.NoSuchElementException;
import java.util.function.Function;

/**
 * A union type contains a value that can be one of two types. It is also called
 * the "sum" type sometimes. Union containers are immutable.
 *
 * A union element contains a single reference that can be of type A or of type
 * B. The pure functions {@link #isFirst()} and {@link #isSecond()} can be used
 * to check if stored reference is of the respective types. The functions
 * {@link #getFirst()} and {@link #getSecond()} can be used to retrieve the
 * value with the respective type. An exception is raised if {@link #getFirst()}
 * is invoked while {@link #isFirst()} returns false.
 *
 * @see java.util.Optional
 * @see Pair
 *
 * @param <A> the type for the first alternative
 * @param <B> the type for the second alternative
 */
public class Union<A, B> {

    private final boolean isFirst;
    private final Object value;

    /**
     * private constructor the static methods {@link #fromFirst(Object)} and
     * {@link #fromSecond(Object)}.
     *
     * @param value the value to store, may be null
     * @param isFirst true if of first, false if of second type
     */
    private Union(Object value, boolean isFirst) {
        this.value = value;
        this.isFirst = isFirst;
    }

    /**
     * Instantiate a new union type with the value stored from the first type.
     *
     * The result will return true for {@link #isFirst()}.
     *
     * @param value the value to store, may be null
     * @return a freshly created immutable union object.
     * @param <A> the type of the first alternative
     * @param <B> the type of the second alternative
     */
    public static <A, B> Union<A, B> fromFirst(A value) {
        return new Union<A, B>(value, true);
    }

    /**
     * Instantiate a new union type with the value stored from the second type.
     *
     * The result will return true for {@link #isSecond()}.
     *
     * @param value the value to store, may be null
     * @return a freshly created immutable union object.
     * @param <A> the type of the first alternative
     * @param <B> the type of the second alternative
     */
    public static <A, B> Union<A, B> fromSecond(B value) {
        return new Union<A, B>(value, false);
    }

    /**
     * Returns if this union object has been created using
     * {@link #fromFirst(Object)}.
     *
     * @return true iff this union object has created using
     *         {@link #fromFirst(Object)}.
     */
    public boolean isFirst() {
        return isFirst;
    }

    /**
     * Returns if this union object has been created using
     * {@link #fromSecond(Object)}.
     *
     * @return true iff this union object has created using
     *         {@link #fromSecond(Object)}.
     */
    public boolean isSecond() {
        return !isFirst;
    }

    /**
     * Returns the stored value (of type A) if this object has been created
     * using {@link #fromFirst(Object)}. Throws a
     * {@link NoSuchElementException} otherwise.
     *
     * @return the stored value, may be null
     */
    public A getFirst() {
        if (isFirst) {
            return (A) value;
        } else {
            throw new NoSuchElementException();
        }
    }

    /**
     * Returns the stored value (of type B) if this object has been created
     * using {@link #fromSecond(Object)}. Throws a
     * {@link NoSuchElementException} otherwise.
     *
     * @return the stored value, may be null
     */
    public B getSecond() {
        if (!isFirst) {
            return (B) value;
        } else {
            throw new NoSuchElementException();
        }
    }

    /**
     * Create a new union object. If {@link #isFirst()} returns true, then
     * the function is applied to the value, if not the value remains untouched.
     *
     * @param function non-null function to apply to the value
     * @return a fresh union object
     * @param <C> the result type of function
     */
    public <C> Union<C, B> mapFirst(Function<A, C> function) {
        if (isFirst()) {
            return fromFirst(function.apply(getFirst()));
        } else {
            return (Union<C, B>) this;
        }
    }

    /**
     * Create a new union object. If {@link #isSecond()} returns true, then
     * the function is applied to the value, if not the value remains untouched.
     *
     * @param function non-null function to apply to the value
     * @return a fresh union object
     * @param <C> the result type of function
     */
    public <C> Union<A, C> mapSecond(Function<B, C> function) {
        if (isSecond()) {
            return fromSecond(function.apply(getSecond()));
        } else {
            return (Union<A, C>) this;
        }
    }

    @Override
    public String toString() {
        return "Union{" + (isFirst ? "first" : "second") +
            " alternative, value=" + value +
            '}';
    }
}
