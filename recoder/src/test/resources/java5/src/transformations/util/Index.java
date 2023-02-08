// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

import java.util.Enumeration;
import java.util.NoSuchElementException;

// to do: make Serializable

/**
 * Implements an object-to-index assignment. An object can be assigned a long
 * value. This is required to avoid repeated creations of pseudo objects
 * representing numbers.
 * 
 * @author RN
 */
public class Index implements Cloneable {

    static class Entry {
        int hash;

        Object key;

        long value;

        Entry next;

        public Entry(int hash, Object key, long value, Entry next) {
            this.hash = hash;
            this.key = key;
            this.value = value;
            this.next = next;
        }

        protected Object clone() {
            return new Entry(hash, key, value, (next != null) ? (Entry) next.clone() : null);
        }
    }

    private transient Entry table[];

    private transient int count;

    private transient int ld;

    private final HashCode hasher;

    public Index() {
        this(null, 8);
    }

    public Index(HashCode hasher) {
        this(hasher, 8);
    }

    public Index(int initialCapacity) {
        this(null, initialCapacity);
    }

    public Index(HashCode hasher, int initialCapacity) {
        this.hasher = (hasher != null) ? hasher : HashCode.NATURAL;
        if (initialCapacity < 4)
            initialCapacity = 4;
        ld = 2;
        int cap = 4;
        while (cap < initialCapacity) {
            ld += 1;
            cap += cap;
        }
        table = new Entry[cap];
        ld = 32 - ld;
    }

    public int size() {
        return count;
    }

    public boolean isEmpty() {
        return count == 0;
    }

    public Enumeration keys() {
        return new Enumerator(table);
    }

    final void rehash() {
        Entry[] oldMap = table;
        int oldCapacity = oldMap.length;
        int newCapacity = oldCapacity * 2;
        ld -= 1;
        Entry[] newMap = table = new Entry[newCapacity];
        for (int i = oldCapacity; i-- > 0;) {
            Entry e = oldMap[i];
            while (e != null) {
                int index = (-1640531527 * e.hash) >>> ld;
                Entry f = e.next;
                e.next = newMap[index];
                newMap[index] = e;
                e = f;
            }
        }
    }

    public boolean contains(long value) {
        Entry tab[] = table;
        for (int i = tab.length; i-- > 0;) {
            for (Entry e = tab[i]; e != null; e = e.next) {
                if (e.value == value) {
                    return true;
                }
            }
        }
        return false;
    }

    public boolean containsKey(Object key) {
        int hash = hasher.hashCode(key);
        int index = (-1640531527 * hash) >>> ld;
        for (Entry e = table[index]; e != null; e = e.next) {
            if (e.hash == hash && hasher.equals(e.key, key)) {
                return true;
            }
        }
        return false;
    }

    /**
     * retrieves the assigne long value for the given object.
     * 
     * @param key
     *            the objct to look for
     * @return the assigned long value, or -1L if there is none.
     */
    public long get(Object key) {
        int hash = hasher.hashCode(key);
        int index = (-1640531527 * hash) >>> ld;
        for (Entry e = table[index]; e != null; e = e.next) {
            if (e.hash == hash && hasher.equals(e.key, key)) {
                return e.value;
            }
        }
        return -1L;
    }

    /**
     * assigns the given long value to the specified key.
     * 
     * @param key
     *            the object to assign a value to
     * @param value
     *            the long value to be assigned. This value must be greater or
     *            equal to 0
     */
    public long put(Object key, long value) {
        Debug.assertBoolean(value >= 0);
        int hash = hasher.hashCode(key);
        int index = (-1640531527 * hash) >>> ld;
        for (Entry e = table[index]; e != null; e = e.next) {
            if (e.hash == hash && hasher.equals(e.key, key)) {
                long old = e.value;
                e.value = value;
                return old;
            }
        }
        if (count >= table.length) {
            rehash();
            return put(key, value);
        }
        table[index] = new Entry(hash, key, value, table[index]);
        count++;
        return -1L;
    }

    public long remove(Object key) {
        int hash = hasher.hashCode(key);
        int index = (-1640531527 * hash) >>> ld;
        for (Entry e = table[index], d = null; e != null; d = e, e = e.next) {
            if (e.hash == hash && hasher.equals(e.key, key)) {
                if (d != null) {
                    d.next = e.next;
                } else {
                    table[index] = e.next;
                }
                count--;
                return e.value;
            }
        }
        return -1L;
    }

    public void clear() {
        Entry tab[] = table;
        for (int index = tab.length; --index >= 0;) {
            tab[index] = null;
        }
        count = 0;
    }

    /*
     * public void copyKeysInto(Object[] array) { Entry table[] = this.table;
     * for (int i = 0, j = 0; i < table.length; i++) { Entry entry = table[i];
     * while (entry != null) { array[j++] = entry.key; entry = entry.next; } } }
     * 
     * public void copyValuesInto(Object[] array) { Entry table[] = this.table;
     * for (int i = 0, j = 0; i < table.length; i++) { Entry entry = table[i];
     * while (entry != null) { array[j++] = entry.value; entry = entry.next; } } }
     */

    public Object clone() {
        try {
            Index t = (Index) super.clone();
            t.table = new Entry[table.length];
            for (int i = table.length; i-- > 0;) {
                t.table[i] = (table[i] != null) ? (Entry) table[i].clone() : null;
            }
            return t;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }

    public String toString() {
        int max = size() - 1;
        StringBuffer buf = new StringBuffer();
        Enumeration k = keys();
        buf.append("{");
        for (int i = 0; i <= max; i++) {
            Object key = k.nextElement();
            buf.append(key.toString() + "=" + get(key));
            if (i < max) {
                buf.append(", ");
            }
        }
        buf.append("}");
        return buf.toString();
    }

    private static class Enumerator implements Enumeration {
        int index;

        Entry table[];

        Entry entry;

        Enumerator(Entry table[]) {
            this.table = table;
            this.index = table.length;
        }

        public boolean hasMoreElements() {
            if (entry != null) {
                return true;
            }
            while (index-- > 0) {
                if ((entry = table[index]) != null) {
                    return true;
                }
            }
            return false;
        }

        public Object nextElement() {
            if (entry == null) {
                while ((index-- > 0) && ((entry = table[index]) == null))
                    ;
            }
            if (entry != null) {
                Entry e = entry;
                entry = e.next;
                return e.key;
            }
            throw new NoSuchElementException("Enumerator");
        }
    }
}