// This file is part of the RECODER library and protected by the LGPL

package recoder.util;

import java.util.Enumeration;

/**
 * this class is a simple wrapper for the data structure Queue, which provides
 * slightly more funnctionality, such as avoiding duplicates or building length
 * statistics.
 * 
 * @author RN
 */
public class Worklist {

    /** should it be possible to add items to the worklist twice? */
    protected boolean allowDuplicates;

    /** records thw maximum length of the worklist */
    protected int maxLen = 0;

    /** the queue that implements the worklist */
    Queue impl = new Queue(HashCode.IDENTITY);

    /** creates a new empty worklist */
    public Worklist() {
        this(true);
    }

    /**
     * creates a new empty worklist.
     * 
     * @param allowDuplicates
     *            indicates whether or not to allow duplicate items
     */
    public Worklist(boolean allowDuplicates) {
        this.allowDuplicates = allowDuplicates;
        impl.setAllowShrink(false);
    }

    /** determines whether the worklist is empty or not. */
    public final boolean isEmpty() {
        return impl.isEmpty();
    }

    /**
     * adds the given item to the worklist. If the worklist does not allow
     * duplicates and the item is already contained, it is ignored.
     * 
     * @param todo
     *            the item to be added
     */
    public void addItem(Object todo) {
        addItem(todo, allowDuplicates);
    }

    /**
     * adds the given item to the worklist, overriding the default duplicate
     * handling strategy.
     * 
     * @param todo
     *            the item to be added
     * @param allowDuplicates
     *            indicates whether there may be duplicates of the item or not
     */
    public void addItem(Object todo, boolean allowDuplicates) {
        if (allowDuplicates || !contains(todo)) {
            impl.enqueue(todo);
            int len = size();
            if (len > maxLen) {
                maxLen = len;
            }
        }
    }

    /**
     * retrieves the first item from the worklist
     * 
     * @return the first item of the list or <tt>null</tt> if the list is
     *         empty
     */
    public Object getItem() {
        if (isEmpty()) {
            return null;
        } else {
            return impl.first();
        }
    }

    /**
     * removes the first item from the worklist and returns the removed item. If
     * the worklist is empty, the method returns <tt>null</tt>.
     * 
     * @return the removed item (the former first item) or <tt>null</tt> if
     *         the list was empty
     */
    public Object removeItem() {
        return impl.dequeue();
    }

    /**
     * determines whether or not the worklist contains some element
     * 
     * @return true if there is at least one element in the list
     */
    public boolean contains(Object x) {
        return impl.contains(x);
    }

    /**
     * returns an enumeration of the elements within the list.
     * 
     * @return a java.util.Enumeration object
     */
    public Enumeration elements() {
        return impl.elements();
    }

    /**
     * determines the number of items in the worklist.
     * 
     * @return the size of the worklist
     */
    public int size() {
        return impl.size();
    }

    /** returns the (historical) maximum length of the list */
    public int getMaximumLength() {
        return maxLen;
    }

}