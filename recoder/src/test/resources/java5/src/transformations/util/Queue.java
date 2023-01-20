// This file is part of the RECODER library and protected by the LGPL

package recoder.util;

import java.util.Enumeration;
import java.util.NoSuchElementException;

/**
 * This class implements a simple FIFO using a dynamically growing and shrinking
 * array.
 * 
 * @author RN
 */
public class Queue {

    private final static int DEFAULT_INITIAL_CAPACITY = 32;

    private final static Equality DEFAULT_EQUALITY = HashCode.NATURAL;

    /** the equality relation to be used for element comparison */
    protected Equality equality;

    /** the data array */
    protected Object[] data;

    /** allow shrinking */
    protected boolean allowShrink = true;

    /** the index of the first element or -1 if the queue is empty */
    protected int start;

    /** the insdex of the last element or -1 if the queue is empty */
    protected int end;

    public Queue() {
        this(DEFAULT_INITIAL_CAPACITY, DEFAULT_EQUALITY);
    }

    public Queue(int initialCapacity) {
        this(initialCapacity, DEFAULT_EQUALITY);
    }

    public Queue(Equality equality) {
        this(DEFAULT_INITIAL_CAPACITY, equality);
    }

    public Queue(int initialCapacity, Equality equality) {
        data = new Object[initialCapacity];
        this.equality = equality;
        start = -1;
        end = -1;
    }

    public int capacity() {
        return data.length;
    }

    public int size() {
        if (start == -1) {
            return 0;
        } else if (start > end) {
            return data.length - (start - (end + 1));
        } else {
            return end - start + 1;
        }
    }

    /**
     * copies the data array to the given array. Data in the new array starts at
     * position 0. It is assumed, that the new array has a suitable size.
     * 
     * @param dest
     *            the destination array
     */
    private void copyArray(Object[] dest) {
        int size = size();
        if (size > 0) {
            if (start <= end) {
                System.arraycopy(data, start, dest, 0, size);
            } else {
                int l1 = data.length - start;
                System.arraycopy(data, start, dest, 0, l1);
                System.arraycopy(data, 0, dest, l1, end + 1);
            }
        }
    }

    /** doubles the data array size and "normalizes" the indicees. */
    private void grow() {
        int newSize = data.length * 2;
        if (newSize == 0) {
            newSize = 1;
        }
        Object[] newData = new Object[newSize];
        if (start != -1) {
            copyArray(newData);
            end = size() - 1;
            start = 0;
        }
        data = newData;
    }

    public void setAllowShrink(boolean allow) {
        allowShrink = allow;
    }

    /** reduces the data array size and "normalizes" the indicees. */
    private void shrink() {
        if (data.length > 31) {
            Object[] newData = new Object[data.length / 2];
            if (start != -1) {
                copyArray(newData);
                end = size() - 1;
                start = 0;
            }
            data = newData;
        }
    }

    public final boolean isEmpty() {
        return start == -1;
    }

    public void enqueue(Object x) {
        if (size() == data.length) {
            grow();
        }
        if (isEmpty()) {
            start = 0;
            end = 0;
            data[0] = x;
        } else {
            if (end < data.length - 1) {
                data[++end] = x;
            } else {
                end = 0;
                data[0] = x;
            }
        }
    }

    public Object dequeue() {
        if (isEmpty()) {
            return null;
        } else {
            Object result = data[start];
            if (start == end) {
                start = -1;
                end = -1;
            } else {
                if (start < data.length - 1) {
                    start++;
                } else {
                    start = 0;
                }
            }
            if (allowShrink && (size() < data.length / 3)) {
                shrink();
            }
            return result;
        }
    }

    public Object first() {
        if (start != -1) {
            return data[start];
        } else {
            return null;
        }
    }

    public boolean contains(Object x) {
        if (isEmpty() || (x == null)) {
            return false;
        }
        boolean result = false;
        if (start <= end) {
            for (int i = start; (i <= end) && !result; i++) {
                result = equality.equals(data[i], x);
            }
        } else {
            for (int i = start; (i < data.length) && !result; i++) {
                result = equality.equals(data[i], x);
            }
            for (int i = 0; (i <= end) && !result; i++) {
                result = equality.equals(data[i], x);
            }
        }
        return result;
    }

    public Enumeration elements() {
        return new QueueEnumeration();
    }

    protected class QueueEnumeration implements Enumeration {

        int currPos;

        boolean more;

        public QueueEnumeration() {
            currPos = start;
            more = start != -1;
        }

        public boolean hasMoreElements() {
            return more;
        }

        public Object nextElement() throws NoSuchElementException {
            if (!more) {
                throw new NoSuchElementException();
            } else {
                Object result = data[currPos];
                if (currPos == end) {
                    more = false;
                } else {
                    currPos++;
                    if (currPos == data.length) {
                        currPos = 0;
                    }
                }
                return result;
            }
        }

    }

}