package org.key_project.util.collection;

import org.key_project.util.EqualsModProofIrrelevancy;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collector;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 * List interface to be implemented by non-destructive lists
 */
public interface ImmutableList<T>
        extends Iterable<T>, java.io.Serializable, EqualsModProofIrrelevancy {

    /**
     * Returns a Collector that accumulates the input elements into a new ImmutableList.
     *
     * @return a Collector that accumulates the input elements into a new ImmutableList.
     */
    public static <T> Collector<T, List<T>, ImmutableList<T>> collector() {
        return Collector.of(LinkedList<T>::new, (list, el) -> list.add(el), (list1, list2) -> {
            list1.addAll(list2);
            return list1;
        }, ImmutableList::<T>fromList);
    }

    /**
     * Creates an ImmutableList from a List.
     *
     * @param list a List.
     * @return an ImmutableList containing the same elements as the specified list.
     */
    public static <T> ImmutableList<T> fromList(Collection<T> list) {
        ImmutableList<T> result = ImmutableSLList.nil();

        for (T el : list) {
            result = result.append(el);
        }

        return result;
    }

    /**
     * prepends element to the list (non-destructive)
     *
     * @param element the head of the created list
     * @return IList<T> with the new element as head and this list as tail
     */
    ImmutableList<T> prepend(T element);

    /**
     * prepends a whole list (non-destructive)
     *
     * @param list the list to be prepended
     * @return IList<T> list++this
     */

    ImmutableList<T> prepend(ImmutableList<T> list);

    /**
     * prepends an immutable list in reverse order, i.e., [4,5,6].prepend([1,2,3]) will be
     * [3,2,1,4,5,6] (more efficient than {@link ImmutableList#prepend(ImmutableList)})
     *
     * @return reverse(collection)++this
     */
    ImmutableList<T> prependReverse(ImmutableList<T> collection);

    /**
     * prepends an iterable collection in reverse order, i.e., [4,5,6].prepend([1,2,3]) will be
     * [3,2,1,4,5,6]
     *
     * @return reverse(collection)++this
     */
    ImmutableList<T> prependReverse(Iterable<T> collection);

    /**
     * prepends array (O(n))
     *
     * @param array the array of the elements to be prepended
     * @return IList<T> the new list
     */
    ImmutableList<T> prepend(@SuppressWarnings("unchecked") T... array);

    /**
     * appends element to the list (non-destructive)
     *
     * @param element to be added at the end
     * @return IList<T> with the new element at the end
     */
    ImmutableList<T> append(T element);

    /**
     * appends a whole list (non-destructive)
     *
     * @param list the list to be appended
     * @return IList<T> this++list
     */
    ImmutableList<T> append(ImmutableList<T> list);

    /**
     * appends an iterable collection
     */
    ImmutableList<T> append(Iterable<T> collection);

    /**
     * appends element at end (non-destructive) (O(n))
     *
     * @param array the array to be appended
     * @return IList<T> the new list
     */
    ImmutableList<T> append(@SuppressWarnings("unchecked") T... array);

    /**
     * @return <T> the first element in list
     */
    T head();

    /**
     * return true if predicate is fullfilled for at least one element
     *
     * @param predicate the predicate
     * @return true if predicate is fullfilled for at least one element
     */
    boolean exists(Predicate<T> predicate);

    /**
     * @return IList<T> tail of list
     */

    ImmutableList<T> tail();

    /**
     * @return IList<T> this list without the first <code>n</code> elements
     */
    ImmutableList<T> take(int n);

    /**
     * Reverses this list
     */
    ImmutableList<T> reverse();

    /**
     * @return Iterator<T> of this list
     */
    @Override
    Iterator<T> iterator();

    /**
     * @return boolean is true iff. obj is in List
     */
    boolean contains(T obj);

    /**
     * @return int representing number of elements in list
     */

    int size();

    /**
     * @return true iff the list is empty
     */
    boolean isEmpty();

    /**
     * removes first occurrence of obj
     *
     * @return new list
     */
    ImmutableList<T> removeFirst(T obj);

    /**
     * removes all occurrences of obj
     *
     * @return new list
     */
    ImmutableList<T> removeAll(T obj);

    /**
     * Convert the list to a Java array (O(n))
     */
    <S> S[] toArray(S[] array);

    /**
     * Convert the list to a Java array (O(n))
     */
    <S> S[] toArray(Class<S> type);


    /**
     * A stream object for this collection.
     *
     * @return a non-null stream object
     */
    default Stream<T> stream() {
        return StreamSupport.stream(this.spliterator(), false);
    }

    /**
     * Convert an {@link ImmutableList} to a {@link List}.
     *
     * @return This element converted to a {@link List}.
     */
    default List<T> toList() {
        List<T> result = new ArrayList<>();
        Iterator<T> it = iterator();
        while (it.hasNext()) {
            result.add(it.next());
        }
        return result;
    }

    default boolean hasPrefix(ImmutableList<T> other) {
        if (other.size() > this.size()) {
            return false;
        }
        if (other.size() == 0) {
            return true;
        }
        if (Objects.equals(head(), other.head())) {
            return tail().hasPrefix(other.tail());
        } else {
            return false;
        }
    }

    default ImmutableList<T> stripPrefix(ImmutableList<T> prefix) {
        if (prefix.isEmpty()) {
            return this;
        }
        if (!hasPrefix(prefix)) {
            throw new IllegalArgumentException("not a prefix of this list");
        }
        return this.tail().stripPrefix(prefix.tail());
    }

    default T last() {
        if (isEmpty()) {
            throw new IllegalStateException("last() called on empty list");
        }
        if (tail().isEmpty()) {
            return head();
        }
        return tail().last();
    }

    @Override
    default boolean equalsModProofIrrelevancy(Object obj) {
        if (!(obj instanceof ImmutableList)) {
            return false;
        }
        var that = (ImmutableList<?>) obj;
        if (size() != that.size()) {
            return false;
        }
        var self = this;
        while (!self.isEmpty()) {
            var obj1 = self.head();
            var obj2 = that.head();
            if (!(obj1 instanceof EqualsModProofIrrelevancy)) {
                return false;
            }
            if (!(obj2 instanceof EqualsModProofIrrelevancy)) {
                return false;
            }
            if (!((EqualsModProofIrrelevancy) obj1).equalsModProofIrrelevancy(obj2)) {
                return false;
            }
            self = self.tail();
            that = that.tail();
        }
        return true;
    }

    @Override
    default int hashCodeModProofIrrelevancy() {
        var self = this;
        var hashcode = Objects.hash(this.size());
        while (!self.isEmpty()) {
            if (self.head() instanceof EqualsModProofIrrelevancy) {
                hashcode = Objects.hash(hashcode,
                        ((EqualsModProofIrrelevancy) self.head()).hashCodeModProofIrrelevancy());
            } else {
                hashcode = Objects.hash(hashcode, self.head());
            }
            self = self.tail();
        }
        return hashcode;
    }
}
