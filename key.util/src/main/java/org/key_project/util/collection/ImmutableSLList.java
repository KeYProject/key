/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.lang.reflect.Array;
import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Collector;

import org.key_project.util.Strings;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Simple implementation of a non-destructive (unmodifiable) list. The list implementation allows
 * list sharing of sublists.
 *
 * The costs of the different operations are O(1) for prepending one element, O(m) for prepending a
 * list with m elements, O(n) for appending an element to this list(size n) O(n) for appending a
 * list with m elements to this list (size n) head() has O(1) tail has O(1) size has O(1) ATTENTION
 * appending and prepending and element can be realized with O(1) costs (see Osaka) then having tail
 * and head with amortized O(1). This will be done later (if necessary).
 */
@SuppressWarnings({ "unchecked" })
public abstract class ImmutableSLList<T extends @Nullable Object> implements ImmutableList<T> {

    /**
     * generated serial id
     */
    private static final long serialVersionUID = 8717813038177120287L;
    private static final Logger log = LoggerFactory.getLogger(ImmutableSLList.NIL.class);

    /** the empty list */
    public static <T extends @Nullable Object> ImmutableSLList<T> nil() {
        return (ImmutableSLList<T>) NIL.NIL;
    }

    public static <T extends @Nullable Object> ImmutableSLList<T> singleton(T obj) {
        return new Cons<>(obj, nil());
    }

    /**
     * Reverses this list (O(N))
     */
    @Override
    public ImmutableList<T> reverse() {
        if (size() <= 1) {
            return this;
        }

        ImmutableList<T> rest = this;
        ImmutableList<T> rev = nil();
        while (!rest.isEmpty()) {
            rev = rev.prepend(rest.head());
            rest = rest.tail();
        }
        return rev;
    }

    /**
     * Convert the list to a Java array (O(n))
     */
    @Override
    public <S extends @Nullable Object> S[] toArray(S[] array) {
        S[] result;
        if (array.length < size()) {
            Class<? extends Object[]> arrayClass = array.getClass();
            assert arrayClass.isArray()
                    : "@AssumeAssertion(nullness): This has indeed a component type";
            result = (S[]) Array.newInstance(arrayClass.getComponentType(), size());
        } else {
            result = array;
        }
        ImmutableList<T> rest = this;
        for (int i = 0, sz = size(); i < sz; i++) {
            result[i] = (S) rest.head();
            rest = rest.tail();
        }
        return result;
    }

    /**
     * Convert the list to a Java array (O(n))
     */
    @Override
    @SuppressWarnings("nullness")
    public <S extends @Nullable Object> S[] toArray(Class<S> type) {
        S[] result = (S[]) Array.newInstance(type, size());
        ImmutableList<T> rest = this;
        for (int i = 0, sz = size(); i < sz; i++) {
            // @ assert !rest.isEmpty();
            T head = rest.head();
            result[i] = (S) type.cast(head);
            rest = rest.tail();
        }
        return result;
    }


    /**
     * prepends array (O(n))
     *
     * @param array the array of the elements to be prepended
     * @return IList<T> the new list
     */
    @Override
    public ImmutableList<T> prepend(T... array) {
        return prepend(array, array.length);
    }


    /**
     * prepends the first <code>n</code> elements of an array (O(n))
     *
     * @param array the array of the elements to be prepended
     * @param n an int specifying the number of elements to be prepended
     * @return IList<T> the new list
     */
    protected ImmutableList<T> prepend(T[] array, int n) {
        ImmutableSLList<T> res = this;
        while (n-- != 0) {
            res = new Cons<>(array[n], res);
        }
        return res;
    }


    @Override
    public ImmutableList<T> append(Iterable<T> collection) {
        ImmutableList<T> tmp = this;
        for (T elem : collection) {
            tmp = tmp.append(elem);
        }
        return tmp;
    }

    @Override
    public ImmutableList<T> prependReverse(Iterable<T> collection) {
        ImmutableSLList<T> tmp = this;
        for (T elem : collection) {
            tmp = new Cons<>(elem, tmp);
        }
        return tmp;
    }


    /**
     * first <code>n</code> elements of the list are truncated
     *
     * @param n an int specifying the number of elements to be truncated
     * @return IList<T> this list without the first <code>n</code> elements
     */
    @Override
    public ImmutableList<T> take(int n) {
        if (n < 0 || n > size()) {
            throw new IndexOutOfBoundsException(
                "Unable to take " + n + " elements from list " + this);
        }

        ImmutableList<T> rest = this;

        while (n-- != 0) {
            rest = rest.tail();
        }

        return rest;
    }


    private static class Cons<S extends @Nullable Object> extends ImmutableSLList<S> {

        /**
         *
         */
        private static final long serialVersionUID = 2377644880764534935L;

        /** the first element */
        private final S element;
        /** reference to the next element (equiv.to the tail of list) */
        private final ImmutableSLList<S> cons;
        /** size of the list */
        private final int size;

        /**
         * new list with only one element
         *
         * @param element the only element in list
         */
        Cons(S element) {
            this.element = element;
            cons = nil();
            size = 1;
        }

        /**
         * constructs a new list with element as head and cons as tail
         *
         * @param element a <T> stored in the head element of the list
         * @param cons tail of the list
         */
        Cons(S element, ImmutableSLList<S> cons) {
            this.element = element;
            this.cons = cons;
            size = cons.size() + 1;
        }

        /**
         * creates a new list with element as head and the momentan list as tail (O(1))
         *
         * @param e the <T> to be prepended
         * @return IList<T> the new list
         */
        @Override
        public ImmutableList<S> prepend(S e) {
            return new Cons<>(e, this);
        }

        /**
         * prepends list (O(n)+O(m))
         *
         * @param list the IList<T> to be prepended
         * @return IList<T> the new list
         */
        @Override
        public ImmutableList<S> prepend(ImmutableList<S> list) {
            if (list.isEmpty()) {
                return this;
            } else {
                final int sz = list.size();
                if (sz == 1) {
                    // @ assert !list.isEmpty();
                    @SuppressWarnings("nullness")
                    @NonNull
                    S head = list.head();
                    return new Cons<>(head, this);
                }
                Cons<S> result = this;
                final Object[] listElements = list.toArray(new Object[sz]);
                for (int i = sz - 1; i >= 0; i--) {
                    result = new Cons<>((S) listElements[i], result);
                }
                return result;
            }
        }

        /**
         * prepends list (O(n)+O(m)) in reversed order
         *
         * @param list the IList<T> to be prepended
         * @return IList<T> the new list
         */
        @Override
        public ImmutableList<S> prependReverse(ImmutableList<S> list) {
            if (list.isEmpty()) {
                return this;
            } else {
                Cons<S> result = this;
                for (int sz = list.size(); sz > 0; sz--) {
                    assert !list.isEmpty() : "@AssumeAssertion(nullness): Invariant";
                    result = new Cons<>(list.head(), result);
                    list = list.tail();
                }
                return result;
            }
        }

        /**
         * return true if predicate is fullfilled for at least one element
         *
         * @param predicate the predicate
         * @return true if predicate is fullfilled for at least one element
         */
        @Override
        public boolean exists(Predicate<? super S> predicate) {
            ImmutableList<S> list = this;
            while (!list.isEmpty()) {
                if (predicate.test(list.head())) {
                    return true;
                }
                list = list.tail();
            }
            return false;
        }


        /**
         * appends element at end (non-destructive) (O(n))
         *
         * @param e the <T> to be prepended
         * @return IList<T> the new list
         */
        @Override
        public ImmutableList<S> append(S e) {
            return new Cons<S>(e).prepend(this);
        }

        /**
         * appends element at end (non-destructive) (O(n))
         *
         * @param list the IList<T> to be appended
         * @return IList<T> the new list
         */
        @Override
        public ImmutableList<S> append(ImmutableList<S> list) {
            return list.prepend(this);
        }

        /**
         * appends element at end (non-destructive) (O(n))
         *
         * @param array the array to be appended
         * @return IList<T> the new list
         */
        @Override
        public ImmutableList<S> append(S... array) {
            return ((ImmutableList<S>) nil()).prepend(array).prepend(this);
        }

        /** @return <T> first element in list */
        @Override
        public S head() {
            return element;
        }

        /** @return IList<T> tail of the list */
        @Override
        public ImmutableList<S> tail() {
            return cons;
        }

        /**
         * hashcode for collections, implemented similar (just reverse) algorithm as
         * java.util.Collections use
         *
         * @return the hashcode of the list
         */
        @Override
        public int hashCode() {
            int hashCode = 0;
            ImmutableList<S> crt = this;

            while (!crt.isEmpty()) {
                final S element = crt.head();
                hashCode = (element == null ? 0 : element.hashCode()) + 31 * hashCode;
                crt = crt.tail();
            }
            return hashCode;
        }


        /** @return iterator through list */
        @Override
        public Iterator<S> iterator() {
            return new SLListIterator<>(this);
        }

        /** @return int the number of elements in list */
        @Override
        public int size() {
            return size;
        }

        /** @return boolean true iff. obj in list */
        @Override
        public boolean contains(S obj) {
            ImmutableList<S> list = this;
            S t;
            while (!list.isEmpty()) {
                t = list.head();
                if (Objects.equals(t, obj)) {
                    return true;
                }
                list = list.tail();
            }
            return false;
        }

        /** @return true iff the list is empty */
        @Override
        public boolean isEmpty() {
            return false;
        }


        /**
         * removes first occurrences of obj (O(n))
         *
         * @return new list
         */
        @Override
        public ImmutableList<S> removeFirst(S obj) {
            S[] res = (S[]) new Object[size()];
            int i = 0;
            ImmutableSLList<S> rest = this;
            ImmutableSLList<S> unmodifiedTail;
            S t;
            while (!rest.isEmpty()) {
                t = rest.head();
                rest = (ImmutableSLList<S>) rest.tail();
                if (!(Objects.equals(t, obj))) {
                    res[i++] = t;
                } else {
                    unmodifiedTail = rest;
                    return unmodifiedTail.prepend(res, i);
                }
            }
            return this;
        }


        /**
         * removes all occurrences of obj (O(n))
         *
         * @return new list
         */
        @Override
        public ImmutableList<S> removeAll(S obj) {
            S[] res = (S[]) new Object[size()];
            int i = 0;
            ImmutableSLList<S> rest = this;
            ImmutableSLList<S> unmodifiedTail = this;
            S t;

            while (!rest.isEmpty()) {
                t = rest.head();
                rest = (ImmutableSLList<S>) rest.tail();
                if (!(Objects.equals(t, obj))) {
                    res[i++] = t;
                } else {
                    unmodifiedTail = rest;
                }
            }

            return unmodifiedTail.prepend(res, i - unmodifiedTail.size());
        }


        @Override
        public boolean equals(@Nullable Object o) {
            if (!(o instanceof ImmutableList)) {
                return false;
            }
            final ImmutableList<S> o1 = (ImmutableList<S>) o;
            if (o1.size() != size()) {
                return false;
            }

            final Iterator<S> p = iterator();
            final Iterator<S> q = o1.iterator();
            while (p.hasNext()) {
                S ep = p.next();
                S eq = q.next();
                if ((ep == null && eq != null) || (ep != null && !ep.equals(eq))) {
                    return false;
                }
            }
            return true;
        }


        @Override
        public String toString() {
            return Strings.formatAsList(this, "[", ",", "]");
        }
    }

    /** iterates through a none destructive list */
    private static class SLListIterator<T extends @Nullable Object> implements Iterator<T> {

        /** the list of remaining elements */
        private ImmutableList<T> list;

        /**
         * constructs the iterator
         *
         * @param list the IList<T> that has to be iterated
         */
        public SLListIterator(ImmutableList<T> list) {
            this.list = list;
        }

        /** @return next element in list */
        @Override
        public T next() {
            // TODO Perhaps add a RT and throw NuSuchElement to make type checker happy.
            final T element = list.head();
            list = list.tail();
            return element;
        }

        /**
         * @return true iff there are unseen elements in the list
         */
        @Override
        public boolean hasNext() {
            return !list.isEmpty();
        }

        /**
         * throws an unsupported operation exception as removing elements is not allowed on
         * immutable lists
         */
        @Override
        public void remove() {
            throw new UnsupportedOperationException("Removing elements via an iterator"
                + " is not supported for immutable datastructures.");
        }

    }


    private static class NIL<S> extends ImmutableSLList<S> {

        final static ImmutableList<?> NIL = new NIL<>();

        /**
         * serial id
         */
        private static final long serialVersionUID = -4070450212306526804L;

        private final transient Iterator<S> iterator = new SLNilListIterator();

        private NIL() {
        }

        /**
         * the NIL list is a singleton. Deserialization builds a new NIL object that has to be
         * replaced by the singleton.
         */
        private Object readResolve() throws java.io.ObjectStreamException {
            return nil();
        }

        @Override
        public int size() {
            return 0;
        }

        @Override
        public boolean equals(@Nullable Object o) {
            return o instanceof NIL<?>;
        }

        @Override
        public int hashCode() {
            return 0;
        }

        @Override
        public ImmutableList<S> prepend(S element) {
            return new Cons<>(element);
        }

        @Override
        public ImmutableList<S> prepend(ImmutableList<S> list) {
            return list;
        }

        @Override
        public ImmutableList<S> prependReverse(ImmutableList<S> list) {
            return list.reverse();
        }

        @Override
        public ImmutableList<S> append(S element) {
            return new Cons<>(element);
        }

        @Override
        public ImmutableList<S> append(ImmutableList<S> list) {
            return list;
        }

        @Override
        public ImmutableList<S> append(S... array) {
            return prepend(array);
        }

        @Override
        public boolean contains(S obj) {
            return false;
        }

        /**
         * return true if predicate is fullfilled for at least one element
         *
         * @param predicate the predicate
         * @return true if predicate is fullfilled for at least one element
         */
        @Override
        public boolean exists(Predicate<? super S> predicate) {
            return false;
        }

        @Override
        public boolean isEmpty() {
            return true;
        }

        @Override
        public Iterator<S> iterator() {
            return iterator;
        }

        @Override
        public S head() {
            NoSuchElementException ex = new NoSuchElementException();
            log.error("head on NIL!", ex);
            throw ex;
        }

        @Override
        public ImmutableList<S> tail() {
            return this;
        }

        @Override
        public ImmutableList<S> removeAll(S obj) {
            return this;
        }

        @Override
        public ImmutableList<S> removeFirst(S obj) {
            return this;
        }

        @Override
        public String toString() {
            return "[]";
        }

        /** iterates through the a none destructive NIL list */
        private class SLNilListIterator implements Iterator<S> {

            /**
             * creates the NIL list iterator
             */
            public SLNilListIterator() {
            }

            /** @return next element in list */
            @Override
            public S next() {
                throw new NoSuchElementException();
            }

            /**
             * @return true iff there are unseen elements in the list
             */
            @Override
            public boolean hasNext() {
                return false;
            }

            /**
             * throws an unsupported operation exception as removing elements is not allowed on
             * immutable lists
             */
            @Override
            public void remove() {
                throw new UnsupportedOperationException("Removing elements via an iterator"
                    + " is not supported for immutable datastructures.");
            }
        }

    }

    public static <T> Collector<T, List<T>, ImmutableList<T>> toImmutableList() {
        return new ImmutableListCollector<>();
    }

    static class ImmutableListCollector<T> implements Collector<T, List<T>, ImmutableList<T>> {

        @Override
        public Supplier<List<T>> supplier() {
            return ArrayList::new;
        }

        @Override
        public BiConsumer<List<T>, T> accumulator() {
            return List::add;
        }

        @Override
        public BinaryOperator<List<T>> combiner() {
            return (l1, l2) -> {
                l1.addAll(l2);
                return l1;
            };
        }

        @Override
        public Function<List<T>, ImmutableList<T>> finisher() {
            return list -> ImmutableSLList.<T>nil().append(list);
        }

        @Override
        public Set<Characteristics> characteristics() {
            Set<Characteristics> result = new HashSet<>();
            return result;
        }
    }
}
