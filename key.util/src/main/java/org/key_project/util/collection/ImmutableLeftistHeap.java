/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.ArrayDeque;
import java.util.Iterator;

import org.key_project.util.Strings;

/**
 * This class implements the leftist heap, see &quot;Functional Data Structures&quot; by Chris
 * Okasaki
 */
@SuppressWarnings("nullness")
public abstract class ImmutableLeftistHeap<T extends Comparable<T>> implements ImmutableHeap<T> {

    /**
     *
     */
    private static final long serialVersionUID = -4035441830559680469L;



    @SuppressWarnings("unchecked")
    public static <T extends Comparable<T>> ImmutableLeftistHeap<T> nilHeap() {
        return (ImmutableLeftistHeap<T>) Empty.EMPTY_HEAP;
    }


    /**
     * Length of the right spine, i.e. the length of the path from the root to rightmost leaf
     */
    protected abstract int getRightHeight();

    /**
     * Class for non-empty heaps
     */
    private static class Node<S extends Comparable<S>> extends ImmutableLeftistHeap<S> {

        /**
         *
         */
        private static final long serialVersionUID = 4913355498617409303L;

        /**
         * Length of the right spine, i.e. the length of the path from the root to rightmost leaf
         */
        private final int rightHeight;

        private final int size;

        private final S data;

        /**
         * Children of the root of this heap
         */
        private final ImmutableLeftistHeap<S> left;
        private final ImmutableLeftistHeap<S> right;


        /**
         * Node constructor for nodes with only empty children
         */
        public Node(S element) {
            this.rightHeight = 1;
            this.size = 1;
            this.data = element;
            this.left = ImmutableLeftistHeap.nilHeap();
            this.right = ImmutableLeftistHeap.nilHeap();
        }

        /**
         * Node constructor for nodes with at most one non-empty child
         */
        public Node(S element, ImmutableLeftistHeap<S> a) {
            this.rightHeight = 1;
            this.size = 1 + a.size();
            this.data = element;
            this.left = a;
            this.right = ImmutableLeftistHeap.nilHeap();
        }

        /**
         * Node constructor for nodes
         */
        private Node(S element, ImmutableLeftistHeap<S> a, ImmutableLeftistHeap<S> b) {
            data = element;
            size = 1 + a.size() + b.size();
            if (a.getRightHeight() <= b.getRightHeight()) {
                rightHeight = a.getRightHeight() + 1;
                left = b;
                right = a;
            } else {
                rightHeight = b.getRightHeight() + 1;
                left = a;
                right = b;
            }
        }

        /**
         * Length of the right spine, i.e. the length of the path from the root to rightmost leaf
         */
        protected int getRightHeight() {
            return rightHeight;
        }

        /**
         * @return true iff this heap is empty
         */
        public boolean isEmpty() {
            return false;
        }

        /**
         * Add an element to this heap object
         *
         * @param element the element to be added
         * @return a heap that contains all elements of this heap, and additionally
         *         <code>element</code>
         */
        public ImmutableHeap<S> insert(S element) {
            if (element.compareTo(data) <= 0) {
                return new Node<>(element, this);
            } else {
                return new Node<>(data, left, (ImmutableLeftistHeap<S>) right.insert(element));
            }
        }

        /**
         * Add multiple elements to this heap object
         *
         * @param h a heap containing the elements to be added
         * @return a heap that contains all elements of this heap, and additionally all objects from
         *         <code>h</code>
         */
        public ImmutableHeap<S> insert(ImmutableHeap<S> h) {
            if (h.isEmpty()) {
                return this;
            } else if (h instanceof Node<S> other/* <S> */) {
                if (data.compareTo(other.data) <= 0) {
                    return new Node<>(data, left, (ImmutableLeftistHeap<S>) right.insert(other));
                } else {
                    return new Node<>(other.data, other.left,
                        (ImmutableLeftistHeap<S>) insert(other.right));
                }
            } else {
                return insert(h.iterator());
            }
        }

        /**
         * @return the minimum element of this heap, or null iff this heap is empty
         *         (<code>isEmpty()==true</code>)
         */
        public S findMin() {
            return data;
        }

        /**
         * Remove the minimum element from this heap
         *
         * @return a heap that contains all elements of this heap except for the minimum element
         */
        public ImmutableHeap<S> deleteMin() {
            return left.insert(right);
        }

        /**
         * Remove all elements of this heap which are <code>equal</code> to <code>element</code>.
         *
         * @return heap that has all occurrences of <code>element</code> removed
         */
        public ImmutableHeap<S> removeAll(S element) {
            int c = data.compareTo(element);

            if (c > 0) {
                return this;
            }

            ImmutableLeftistHeap<S> newLeft = (ImmutableLeftistHeap<S>) left.removeAll(element);
            ImmutableLeftistHeap<S> newRight = (ImmutableLeftistHeap<S>) right.removeAll(element);

            if (c == 0 && data.equals(element)) {
                return newLeft.insert(newRight);
            }
            if (left == newLeft && right == newRight) {
                return this;
            }
            return new Node<>(data, newLeft, newRight);
        }

        /**
         * @return the number of elements this heap holds
         */
        public int size() {
            return size;
        }

    }

    /**
     * Singleton class for empty heaps
     */
    private static class Empty<S extends Comparable<S>> extends ImmutableLeftistHeap<S> {

        /**
         *
         */
        private static final long serialVersionUID = -2471143956420721016L;

        /**
         * Use this element to construct new heaps
         */
        @SuppressWarnings("rawtypes")
        private static final ImmutableLeftistHeap<?> EMPTY_HEAP = new Empty();

        /**
         * Length of the right spine, i.e. the length of the path from the root to rightmost leaf
         */
        protected int getRightHeight() {
            return 0;
        }

        /**
         * @return true iff this heap is empty
         */
        public boolean isEmpty() {
            return true;
        }

        /**
         * Add an element to this heap object
         *
         * @param element The element to be added
         * @return a heap that contains all elements of this heap, and additionally
         *         <code>element</code>
         */
        public ImmutableHeap<S> insert(S element) {
            return new Node<>(element);
        }

        /**
         * Add multiple elements to this heap object
         *
         * @param h a heap containing the elements to be added
         * @return a heap that contains all elements of this heap, and additionally all objects from
         *         <code>h</code>
         */
        public ImmutableHeap<S> insert(ImmutableHeap<S> h) {
            return h;
        }

        /**
         * @return the minimum element of this heap, or null iff this heap is empty
         *         (<code>isEmpty()==true</code>)
         */
        public S findMin() {
            return null;
        }

        /**
         * Remove the minimum element from this heap
         *
         * @return a heap that contains all elements of this heap except for the minimum element
         */
        public ImmutableHeap<S> deleteMin() {
            return this;
        }

        /**
         * Remove all elements of this heap which are <code>equal</code> to <code>element</code>.
         *
         * @return heap that has all occurrences of <code>element</code> removed
         */
        public ImmutableHeap<S> removeAll(S element) {
            return this;
        }

        /**
         * @return the number of elements this heap holds
         */
        public int size() {
            return 0;
        }

    }

    /**
     * Add multiple elements to this heap object
     *
     * @param elements the elements to be added
     * @return a heap that contains all elements of this heap, and additionally all objects from
     *         <code>elements</code>
     */
    public ImmutableHeap<T> insert(Iterator<T> elements) {
        // Use bottom-up strategy to compose new heap in O(n)

        ArrayDeque<ImmutableHeap<T>> s = new ArrayDeque<>();
        s.push(this);
        while (elements.hasNext()) {
            ImmutableHeap<T> h = new Node<>(elements.next());
            do {
                ImmutableHeap<T> top = s.peek();
                if (h.size() >= top.size()) {
                    h = h.insert(top);
                    s.pop();
                } else {
                    break;
                }
            } while (!s.isEmpty());
            s.push(h);
        }
        ImmutableHeap<T> res = s.pop();
        while (!s.isEmpty()) {
            res = res.insert(s.pop());
        }
        return res;
    }

    /**
     * @return an iterator that returns all elements of this heap
     */
    public Iterator<T> iterator() {
        return new UnsortedIterator<>(this);
    }

    /**
     * @return an iterator that returns all elements of this heap in increasing order
     */
    public Iterator<T> sortedIterator() {
        return new SortedIterator<>(this);
    }


    public String toString() {
        return Strings.formatAsList(this, "[", ",", "]");
    }


    /**
     * Class for iterating the elements of a heap in unspecified order
     */
    private static class UnsortedIterator<T extends Comparable<T>> implements Iterator<T> {

        private final ArrayDeque<Node<T>> remainder = new ArrayDeque<>();

        public UnsortedIterator(ImmutableLeftistHeap<T> heap) {
            push(heap);
        }

        private void push(ImmutableLeftistHeap<T> heap) {
            if (!heap.isEmpty()) {
                remainder.push((Node<T>) heap);
            }
        }

        public boolean hasNext() {
            return !remainder.isEmpty();
        }

        public T next() {
            assert !remainder.isEmpty() : "Missing next element in UnsortedIterator.next()";

            Node<T> heap = remainder.pop();
            // descend in right-first order, this helps to keep the stack small
            push(heap.left);
            push(heap.right);

            return heap.data;
        }

        /**
         * throw an unsupported operation exception as leftiest heaps are immutable
         */
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }


    /**
     * Class for iterating the elements of a heap in increasing order
     */
    private static class SortedIterator<T extends Comparable<T>> implements Iterator<T> {

        private ImmutableHeap<T> remainder;

        public SortedIterator(ImmutableHeap<T> heap) {
            remainder = heap;
        }

        public boolean hasNext() {
            return !remainder.isEmpty();
        }

        public T next() {
            assert !remainder.isEmpty() : "Missing next element in SortedIterator.next()";

            T data = remainder.findMin();
            remainder = remainder.deleteMin();

            return data;
        }

        /**
         * throw an unsupported operation exception as leftist heaps are immutable
         */
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

}
