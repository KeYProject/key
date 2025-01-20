/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java;

import java.util.LinkedList;
import java.util.List;
import java.util.Objects;
import java.util.function.Predicate;

import org.jspecify.annotations.Nullable;

/**
 * Provides static methods to work with arrays.
 *
 * @author Martin Hentschel
 */
public final class ArrayUtil {
    /**
     * Forbid instances by this private constructor.
     */
    private ArrayUtil() {
    }

    /**
     * Searches an element in the given {@link Iterable} instance.
     *
     * Returns the first element that satisfies the predicate.
     *
     * @param array The instance to search in.
     * @param filter The filter to select an element.
     * @return The found element or {@code null} if no element was found.
     */
    public static <T extends @Nullable Object> @Nullable T search(T[] array, Predicate<T> filter) {
        T result = null;
        int i = 0;
        while (result == null && i < array.length) {
            if (filter.test(array[i])) {
                result = array[i];
            }
            i++;
        }
        return result;
    }

    /**
     * <p>
     * Adds the given elements to the existing array. The result is a new array that contains the
     * other elements in the end.
     * </p>
     * <p>
     * <b>Attention: </b> It is not possible to use this method with two {@code null} parameters. In
     * this case is an {@link IllegalArgumentException} thrown.
     * </p>
     *
     * @param array The array to add to.
     * @param toAdd The elements to add.
     * @return The new created array.
     * @throws IllegalArgumentException Both parameters are {@code null}.
     */
    @SuppressWarnings("unchecked")
    public static <T extends @Nullable Object> T[] addAll(T[] array, T[] toAdd) {
        T[] result =
            (T[]) java.lang.reflect.Array.newInstance(getComponentType(array),
                array.length + toAdd.length);
        System.arraycopy(array, 0, result, 0, array.length);
        System.arraycopy(toAdd, 0, result, array.length, toAdd.length);
        return result;
    }

    private static <T extends @Nullable Object> Class<? extends T> getComponentType(T[] array) {
        Class<? extends Object[]> arrayClass = array.getClass();
        assert arrayClass.isArray() : "@AssumeAssertion(nullness): This is always the case";
        return (Class<? extends T>) arrayClass.getComponentType();
    }

    /**
     * <p>
     * Adds the given elements to the existing array. The result is a new array that contains the
     * other elements in the end.
     * </p>
     * <p>
     * <b>Attention: </b> It is not possible to use this method with two {@code null} parameters. In
     * this case is an {@link IllegalArgumentException} thrown.
     * </p>
     *
     * @param array The array to add to.
     * @param toAdd The elements to add.
     * @param newArrayType The type of the new array.
     * @return The new created array.
     * @throws IllegalArgumentException Both parameters are {@code null}.
     */
    @SuppressWarnings("unchecked")
    public static <T extends @Nullable Object> T[] addAll(T[] array, T[] toAdd,
            Class<?> newArrayType) {
        T[] result = (T[]) java.lang.reflect.Array.newInstance(newArrayType,
            array.length + toAdd.length);
        System.arraycopy(array, 0, result, 0, array.length);
        System.arraycopy(toAdd, 0, result, array.length, toAdd.length);
        return result;
    }

    /**
     * <p>
     * Adds the given element to the existing array. The result is a new array that contains one
     * more element.
     * </p>
     * <p>
     * <b>Attention: </b> It is not possible to use this method with two {@code null} parameters. In
     * this case is an {@link IllegalArgumentException} thrown.
     * </p>
     *
     * @param array The array to extend.
     * @param toAdd The element to add.
     * @return The new created array with one more element.
     * @throws IllegalArgumentException Both parameters are {@code null}.
     */
    @SuppressWarnings("unchecked")
    public static <T extends @Nullable Object> T[] add(T[] array, T toAdd) {
        T[] result = (T[]) java.lang.reflect.Array
                .newInstance(getComponentType(array), array.length + 1);
        System.arraycopy(array, 0, result, 0, array.length);
        result[array.length] = toAdd;
        return result;
    }

    /**
     * <p>
     * Adds the given element to the existing array. The result is a new array that contains one
     * more element.
     * </p>
     *
     * @param array The array to extend.
     * @param toAdd The element to add.
     * @return The new created array with one more element.
     */
    public static int[] add(int[] array, int toAdd) {
        int[] result = new int[array.length + 1];
        System.arraycopy(array, 0, result, 0, array.length);
        result[array.length] = toAdd;
        return result;
    }

    /**
     * <p>
     * Inserts the given element at the given index to the existing array. The result is a new array
     * that contains one more element.
     * </p>
     *
     * @param array The array to extend.
     * @param toInsert The element to insert.
     * @param index The index to insert the element at.
     * @return The new created array with one more element.
     */
    @SuppressWarnings("unchecked")
    public static <T extends @Nullable Object> T[] insert(T[] array, T toInsert, int index) {
        T[] result = (T[]) java.lang.reflect.Array
                .newInstance(getComponentType(array), array.length + 1);
        if (index >= 1) {
            System.arraycopy(array, 0, result, 0, index);
        }
        result[index] = toInsert;
        System.arraycopy(array, index, result, index + 1, array.length - index);
        return result;
    }

    /**
     * Checks if the given array contains the element to search.
     *
     * @param <T> The type of the array.
     * @param array The array.
     * @param toSearch The element to search.
     * @return {@code true} if the array contains the element or {@code false} if not or if the
     *         array is {@code null}.
     */
    public static <T extends @Nullable Object> boolean contains(T[] array, T toSearch) {
        return indexOf(array, toSearch) >= 0;
    }

    /**
     * Returns the first index in the given array that contains the element to search. The equality
     * is computed via the comparator. Objects are equal if the comparison result is {@code 0}.
     *
     * @param array The array to search in.
     * @param toSearch The element to search.
     * @return The first index in the array that contains the element to search or {@code -1} if the
     *         elment is not containd in the array.
     */
    public static <T extends @Nullable Object> int indexOf(T[] array, T toSearch) {
        int index = -1;
        for (int i = 0; i < array.length; i++) {
            if (Objects.equals(array[i], toSearch)) {
                return i;
            }
        }
        return index;
    }

    /**
     * Removes all occurrences from toRemove in the array. The equality is computed via the
     * comparator. Objects are equal if the comparison result is {@code 0}.
     *
     * @param array The array to remove from.
     * @param toRemove The element to remove.
     * @return A copy of the array without the element toRemove.
     */
    @SuppressWarnings("unchecked")
    public static <T extends @Nullable Object> T[] remove(T[] array, T toRemove) {
        List<T> result = new LinkedList<>();
        for (T element : array) {
            if (!Objects.equals(element, toRemove)) {
                result.add(element);
            }
        }
        return (T[]) result.toArray((T[]) java.lang.reflect.Array
                .newInstance(getComponentType(array), result.size()));
    }

    /**
     * Converts the given array into a {@link String}.
     *
     * @param array The array to convert.
     * @return The array as {@link String}.
     */
    public static <T extends @Nullable Object> String toString(T[] array) {
        return toString(array, ", ");
    }

    /**
     * Converts the given array into a {@link String}.
     *
     * @param array The array to convert.
     * @param separator The separator between to array elements.
     * @return The array as {@link String}.
     */
    public static <T extends @Nullable Object> String toString(T[] array, String separator) {
        StringBuilder sb = new StringBuilder();
        boolean afterFirst = false;
        for (T element : array) {
            if (afterFirst) {
                sb.append(separator);
            } else {
                afterFirst = true;
            }
            sb.append(element);
        }
        return sb.toString();
    }

    /**
     * Converts the given array into a {@link String}.
     *
     * @param array The array to convert.
     * @return The array as {@link String}.
     */
    public static String toString(int[] array) {
        return toString(array, ", ");
    }

    /**
     * Converts the given array into a {@link String}.
     *
     * @param array The array to convert.
     * @param separator The separator between to array elements.
     * @return The array as {@link String}.
     */
    public static String toString(int[] array, String separator) {
        StringBuilder sb = new StringBuilder();
        boolean afterFirst = false;
        for (int element : array) {
            if (afterFirst) {
                sb.append(separator);
            } else {
                afterFirst = true;
            }
            sb.append(element);
        }
        return sb.toString();
    }

    /**
     * Checks if the given array is empty.
     *
     * @param array The array to check.
     * @return {@code true} array is empty or {@code null}, {@code false} array is not empty.
     */
    public static <T extends @Nullable Object> boolean isEmpty(T[] array) {
        return array.length == 0;
    }
}
