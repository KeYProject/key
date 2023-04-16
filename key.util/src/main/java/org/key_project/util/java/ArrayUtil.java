package org.key_project.util.java;

import java.util.LinkedList;
import java.util.List;
import java.util.Objects;
import java.util.function.Predicate;

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
     * @param array The instance to search in.
     * @param filter The filter to select an element.
     * @return The found element or {@code null} if no element was found.
     */
    public static <T> T search(T[] array, Predicate<T> filter) {
        T result = null;
        if (array != null && filter != null) {
            int i = 0;
            while (result == null && i < array.length) {
                if (filter.test(array[i])) {
                    result = array[i];
                }
                i++;
            }
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
    public static <T> T[] addAll(T[] array, T[] toAdd) {
        if (array != null) {
            if (toAdd != null) {
                T[] result =
                    (T[]) java.lang.reflect.Array.newInstance(array.getClass().getComponentType(),
                        array.length + toAdd.length);
                System.arraycopy(array, 0, result, 0, array.length);
                System.arraycopy(toAdd, 0, result, array.length, toAdd.length);
                return result;
            } else {
                T[] result = (T[]) java.lang.reflect.Array
                        .newInstance(array.getClass().getComponentType(), array.length);
                System.arraycopy(array, 0, result, 0, array.length);
                return result;
            }
        } else {
            if (toAdd != null) {
                T[] result = (T[]) java.lang.reflect.Array
                        .newInstance(toAdd.getClass().getComponentType(), toAdd.length);
                System.arraycopy(toAdd, 0, result, 0, toAdd.length);
                return result;
            } else {
                throw new IllegalArgumentException(
                    "Can not create an array if both paramters are null.");
            }
        }
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
    public static <T> T[] addAll(T[] array, T[] toAdd, Class<?> newArrayType) {
        if (array != null) {
            if (toAdd != null) {
                T[] result = (T[]) java.lang.reflect.Array.newInstance(newArrayType,
                    array.length + toAdd.length);
                System.arraycopy(array, 0, result, 0, array.length);
                System.arraycopy(toAdd, 0, result, array.length, toAdd.length);
                return result;
            } else {
                T[] result = (T[]) java.lang.reflect.Array.newInstance(newArrayType, array.length);
                System.arraycopy(array, 0, result, 0, array.length);
                return result;
            }
        } else {
            if (toAdd != null) {
                T[] result = (T[]) java.lang.reflect.Array.newInstance(newArrayType, toAdd.length);
                System.arraycopy(toAdd, 0, result, 0, toAdd.length);
                return result;
            } else {
                return (T[]) java.lang.reflect.Array.newInstance(newArrayType, 0);
            }
        }
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
    public static <T> T[] add(T[] array, T toAdd) {
        if (array != null) {
            T[] result = (T[]) java.lang.reflect.Array
                    .newInstance(array.getClass().getComponentType(), array.length + 1);
            System.arraycopy(array, 0, result, 0, array.length);
            result[array.length] = toAdd;
            return result;
        } else {
            if (toAdd != null) {
                T[] result = (T[]) java.lang.reflect.Array.newInstance(toAdd.getClass(), 1);
                result[0] = toAdd;
                return result;
            } else {
                throw new IllegalArgumentException(
                    "Can not create an array if both paramters are null.");
            }
        }
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
        if (array != null) {
            int[] result = new int[array.length + 1];
            System.arraycopy(array, 0, result, 0, array.length);
            result[array.length] = toAdd;
            return result;
        } else {
            return new int[] { toAdd };
        }
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
    public static <T> T[] insert(T[] array, T toInsert, int index) {
        if (array != null) {
            T[] result = (T[]) java.lang.reflect.Array
                    .newInstance(array.getClass().getComponentType(), array.length + 1);
            if (index >= 1) {
                System.arraycopy(array, 0, result, 0, index);
            }
            result[index] = toInsert;
            System.arraycopy(array, index, result, index + 1, array.length - index);
            return result;
        } else {
            if (toInsert != null) {
                T[] result = (T[]) java.lang.reflect.Array.newInstance(toInsert.getClass(), 1);
                result[0] = toInsert;
                return result;
            } else {
                throw new IllegalArgumentException(
                    "Can not create an array if array and element to insert are null.");
            }
        }
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
    public static <T> boolean contains(T[] array, T toSearch) {
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
    public static <T> int indexOf(T[] array, T toSearch) {
        int index = -1;
        if (array != null) {
            for (int i = 0; i < array.length; i++) {
                if (Objects.equals(array[i], toSearch)) {
                    return i;
                }
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
     * @return A copy of the array without the element toRemove or {@code null} if the given array
     *         was {@code null}.
     */
    @SuppressWarnings("unchecked")
    public static <T> T[] remove(T[] array, T toRemove) {
        if (array != null) {
            List<T> result = new LinkedList<>();
            for (T element : array) {
                if (!Objects.equals(element, toRemove)) {
                    result.add(element);
                }
            }
            return result.toArray((T[]) java.lang.reflect.Array
                    .newInstance(array.getClass().getComponentType(), result.size()));
        } else {
            return null;
        }
    }

    /**
     * Converts the given array into a {@link String}.
     *
     * @param array The array to convert.
     * @return The array as {@link String}.
     */
    public static <T> String toString(T[] array) {
        return toString(array, ", ");
    }

    /**
     * Converts the given array into a {@link String}.
     *
     * @param array The array to convert.
     * @param separator The separator between to array elements.
     * @return The array as {@link String}.
     */
    public static <T> String toString(T[] array, String separator) {
        StringBuilder sb = new StringBuilder();
        if (array != null) {
            boolean afterFirst = false;
            for (T element : array) {
                if (afterFirst) {
                    sb.append(separator);
                } else {
                    afterFirst = true;
                }
                sb.append(element);
            }
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
        if (array != null) {
            boolean afterFirst = false;
            for (int element : array) {
                if (afterFirst) {
                    sb.append(separator);
                } else {
                    afterFirst = true;
                }
                sb.append(element);
            }
        }
        return sb.toString();
    }

    /**
     * Checks if the given array is empty.
     *
     * @param array The array to check.
     * @return {@code true} array is empty or {@code null}, {@code false} array is not empty.
     */
    public static <T> boolean isEmpty(T[] array) {
        return array == null || array.length == 0;
    }
}
