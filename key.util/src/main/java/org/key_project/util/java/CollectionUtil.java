/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java;

import java.util.*;
import java.util.function.Predicate;

/**
 * Provides static methods to work with {@link Collection}s.
 *
 * @author Martin Hentschel
 */
public class CollectionUtil {
    /**
     * The default separator.
     */
    public static final String SEPARATOR = ", ";

    /**
     * Forbid instances by this private constructor.
     */
    private CollectionUtil() {
    }

    /**
     * Returns the index of the element to search in the given iterator.
     *
     * @param iter The iterator to search in.
     * @param toSearch The element to search.
     * @return The index of the element or {@code -1} if it was not found.
     */
    public static <T> int indexOf(Iterator<T> iter, T toSearch) {
        if (iter != null) {
            int i = 0;
            boolean found = false;
            while (!found && iter.hasNext()) {
                T next = iter.next();
                if (Objects.equals(next, toSearch)) {
                    found = true;
                } else {
                    i++;
                }
            }
            if (found) {
                return i;
            } else {
                return -1;
            }
        } else {
            return -1;
        }
    }

    /**
     * Converts the {@link Collection} into a {@link String}.
     *
     * @param collection The {@link Collection} to convert.
     * @return The {@link Collection} as {@link String}.
     */
    public static String toString(Collection<?> collection) {
        return toString(collection, SEPARATOR);
    }

    /**
     * Converts the {@link Collection} into a {@link String} and uses the defined separator to
     * separate elements.
     *
     * @param collection The {@link Collection} to convert.
     * @param separator The separator between elements.
     * @return The {@link Collection} as {@link String}.
     */
    public static String toString(Collection<?> collection, String separator) {
        StringBuilder sb = new StringBuilder();
        if (collection != null) {
            boolean afterFirst = false;
            for (Object object : collection) {
                if (afterFirst) {
                    if (separator != null) {
                        sb.append(separator);
                    }
                } else {
                    afterFirst = true;
                }
                sb.append(object);
            }
        }
        return sb.toString();
    }

    /**
     * Nullpointersave execution of {@link Collection#isEmpty()}.
     *
     * @param collection The given {@link Collection}.
     * @return {@code true} = is empty or {@code null}, {@code false} = is not empty.
     */
    public static boolean isEmpty(Collection<?> collection) {
        return collection == null || collection.isEmpty();
    }

    /**
     * Nullpointersave execution of {@link Map#isEmpty()}.
     *
     * @param map The given {@link Map}.
     * @return {@code true} = is empty or {@code null}, {@code false} = is not empty.
     */
    public static boolean isEmpty(Map<?, ?> map) {
        return map == null || map.isEmpty();
    }

    /**
     * Adds all elements to the {@link Collection}.
     *
     * @param <T> The type of the {@link Collection}s elements.
     * @param collection The {@link Collection} to add to.
     * @param iterable The elements to add.
     */
    public static <T> void addAll(Collection<T> collection, Iterable<T> iterable) {
        if (collection != null && iterable != null) {
            for (T toAdd : iterable) {
                collection.add(toAdd);
            }
        }
    }

    /**
     * Removes all occurrences of the element in the given {@link Collection}.
     *
     * @param collection The {@link Collection} to remove from.
     * @param toRemove The element to remove.
     * @return {@code true} if at least one element was removed, {@code false} if the
     *         {@link Collection} was not modified.
     */
    public static <T> boolean removeComplete(Collection<T> collection, T toRemove) {
        if (collection != null) {
            Iterator<T> iter = collection.iterator();
            boolean changed = false;
            while (iter.hasNext()) {
                if (Objects.equals(iter.next(), toRemove)) {
                    iter.remove();
                    changed = true;
                }
            }
            return changed;
        } else {
            return false;
        }
    }

    /**
     * Searches all elements accepted by the given {@link IFilter}.
     *
     * @param iterable The {@link Iterable} to search in.
     * @param filter The {@link IFilter} to use.
     * @return The elements accepted by the given {@link Predicate}.
     */
    public static <T> List<T> searchAll(Iterable<T> iterable, Predicate<T> filter) {
        List<T> result = new ArrayList<>();
        if (iterable != null && filter != null) {
            for (T element : iterable) {
                if (filter.test(element)) {
                    result.add(element);
                }
            }
        }
        return result;
    }

    /**
     * Searches an element in the given {@link Iterable} instance.
     *
     * @param iterable The instance to search in.
     * @param filter The filter to select an element.
     * @return The found element or {@code null} if no element was found.
     */
    public static <T> T search(Iterable<T> iterable, Predicate<T> filter) {
        T result = null;
        if (iterable != null && filter != null) {
            Iterator<T> iter = iterable.iterator();
            while (result == null && iter.hasNext()) {
                T next = iter.next();
                if (filter.test(next)) {
                    result = next;
                }
            }
        }
        return result;
    }

    /**
     * Searches an element in the given {@link Iterable} instance and removes the found element from
     * it.
     *
     * @param iterable The instance to search in.
     * @param filter The filter to select an element.
     * @return The found element or {@code null} if no element was found.
     */
    public static <T> T searchAndRemove(Iterable<T> iterable, Predicate<T> filter) {
        T result = null;
        if (iterable != null && filter != null) {
            Iterator<T> iter = iterable.iterator();
            while (result == null && iter.hasNext()) {
                T next = iter.next();
                if (filter.test(next)) {
                    result = next;
                    iter.remove();
                }
            }
        }
        return result;
    }

    /**
     * Searches an element in the given {@link Iterable} instance and removes the found element from
     * it.
     *
     * @param iterable The instance to search in.
     * @param filter The filter to select an element.
     * @return The found element or {@code null} if no element was found.
     */
    public static <T, E extends Throwable> T searchAndRemoveWithException(Iterable<T> iterable,
            IFilterWithException<T, E> filter) throws E {
        T result = null;
        if (iterable != null && filter != null) {
            Iterator<T> iter = iterable.iterator();
            while (result == null && iter.hasNext()) {
                T next = iter.next();
                if (filter.select(next)) {
                    result = next;
                    iter.remove();
                }
            }
        }
        return result;
    }

    /**
     * Checks if the given element is contained in the given {@link Iterable}.
     *
     * @param iterable The given {@link Iterable} to search in.
     * @param element The element to search.
     * @return {@code true} = contained, {@code false} = not contained
     */
    public static <T> boolean contains(Iterable<T> iterable, T element) {
        boolean found = false;
        if (iterable != null) {
            Iterator<T> iter = iterable.iterator();
            while (!found && iter.hasNext()) {
                found = Objects.equals(iter.next(), element);
            }
        }
        return found;
    }

    /**
     * Counts the number of elements in the given {@link Iterable} which are selected by the given
     * {@link IFilter}.
     *
     * @param iterable The elements to count in.
     * @param filter The {@link IFilter} to select elements.
     * @return The number of elements selected by the {@link IFilter} in the given {@link Iterable}.
     */
    public static <T> int count(Iterable<T> iterable, Predicate<T> filter) {
        int count = 0;
        if (iterable != null && filter != null) {
            for (T element : iterable) {
                if (filter.test(element)) {
                    count++;
                }
            }
        }
        return count;
    }

    /**
     * <p>
     * Checks if the given two {@link Collection}s contains the same elements in any order.
     * </p>
     * <p>
     * Empty {@link Collection}s and {@code null} parameters are treated as equal.
     * </p>
     *
     * @param first The first {@link Collection}.
     * @param second The second {@link Collection}.
     * @return {@code true} both {@link Collection}s contains same elements, {@code false}
     *         {@link Collection}s are different.
     */
    public static <T> boolean containsSame(Collection<T> first, Collection<T> second) {
        if (first != null) {
            if (second != null) {
                if (first.size() == second.size()) {
                    Collection<T> firstCopy = new LinkedList<>(first);
                    boolean same = true;
                    Iterator<T> secondIter = second.iterator();
                    while (same && secondIter.hasNext()) {
                        T secondNext = secondIter.next();
                        same = firstCopy.remove(secondNext);
                    }
                    return same;
                } else {
                    return false;
                }
            } else {
                return first.size() == 0;
            }
        } else {
            return second == null || second.size() == 0;
        }
    }

    /**
     * Removes the first element from the given {@link Iterable}.
     *
     * @param iterable The {@link Iterable} to remove first element from.
     * @return The removed first element or {@code null} if no element was removed.
     */
    public static <T> T removeFirst(Iterable<T> iterable) {
        try {
            if (iterable != null) {
                Iterator<T> iter = iterable.iterator();
                T next = iter.next();
                iter.remove();
                return next;
            } else {
                return null;
            }
        } catch (NoSuchElementException e) {
            return null; // Iterable must be empty.
        }
    }

    /**
     * Performs a binary insert on the given <b>sorted</b> {@link List}.
     *
     * @param list The <b>sorted</b> {@link List} to insert in.
     * @param toInsert The element to insert.
     * @param comparator The {@link Comparator} to use.
     */
    public static <T> void binaryInsert(List<T> list, T toInsert, Comparator<T> comparator) {
        if (list.isEmpty()) {
            list.add(toInsert);
        } else {
            int index = Collections.binarySearch(list, toInsert, comparator);
            if (index < 0) {
                index = (index * -1) - 1;
            }
            list.add(index, toInsert);
        }
    }
}
