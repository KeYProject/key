// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

import java.util.Dictionary;
import java.util.Enumeration;
import java.util.NoSuchElementException;

/**
 * @author AL
 */
public abstract class AbstractHashTable extends Dictionary implements MutableMap, HashCode {

    // second half contains values
    Object table[];

    int count;

    int ld;

    private final static float THRESHOLD = 0.75f;

    private final static Object DELETED = new Object() {
        // overwriting this allows us to write "equals(ob, key)"
        // instead of "key != DELETED && equals(ob,key)"
        public boolean equals(Object x) {
            return false;
        }

        public String toString() {
            return "<DELETED>";
        }
    };

    public AbstractHashTable() {
        this(4);
    }

    public AbstractHashTable(int initialCapacity) {
        if (initialCapacity < 4) {
            initialCapacity = 4;
        }
        int cap = 4;
        ld = 2;
        while (cap < initialCapacity) {
            ld += 1;
            cap += cap;
        }
        table = new Object[2 * cap];
        ld = 32 - ld;
    }

    public abstract boolean equals(Object x, Object y);

    public abstract int hashCode(Object x);

    public final int size() {
        return count;
    }

    public final boolean isEmpty() {
        return size() == 0;
    }

    private void rehash() {
        Object[] oldMap = table;
        int oldCapacity = oldMap.length;
        ld -= 1;
        table = new Object[oldCapacity * 2];
        count = 0;
        for (int i = oldCapacity / 2 - 1; i >= 0; i -= 1) {
            Object ob = oldMap[i];
            if (ob != null && ob != DELETED) {
                insert(ob, oldMap[i + oldCapacity / 2]);
            }
        }
    }

    public boolean contains(Object value) {
        if (value == null) {
            throw new NullPointerException();
        }
        Object tab[] = table;
        int voffset = table.length / 2;
        for (int i = voffset; i-- > 0;) {
            Object ob = tab[i];
            if (ob != null && ob != DELETED) {
                if (value.equals(table[voffset + i])) {
                    return true;
                }
            }
        }
        return false;
    }

    public final boolean containsKey(Object key) {
        if (key == null) {
            return false;
        }
        int hash = (-1640531527 * hashCode(key)) >>> ld;
        int index = hash;
        do {
            Object ob = table[index];
            if (ob == null) {
                return false;
            }
            if (equals(ob, key)) {
                return true;
            }
            index = (index + (hash | 1)) & (table.length / 2 - 1);
        } while (index != hash);
        return false;
    }

    public final Object get(Object key) {
        if (key == null) {
            return null;
        }
        int hash = (-1640531527 * hashCode(key)) >>> ld;
        int index = hash;
        do {
            Object ob = table[index];
            if (ob == null) {
                return null;
            }
            if (equals(ob, key)) {
                return table[index + table.length / 2];
            }
            index = (index + (hash | 1)) & (table.length / 2 - 1);
        } while (index != hash);
        return null;
    }

    public final Object put(Object key, Object value) {
        if (key == null) {
            throw new IllegalArgumentException("Null key");
        }
        if (count >= table.length * THRESHOLD / 2) {
            rehash();
        }
        return insert(key, value);
    }

    private Object insert(Object key, Object value) {
        int hash = (-1640531527 * hashCode(key)) >>> ld;
        int index = hash;
        do {
            Object ob = table[index];
            if (ob == null || ob == DELETED) {
                table[index] = key;
                table[index + table.length / 2] = value;
                count += 1;
                return null;
            }
            if (equals(ob, key)) {
                index += table.length / 2;
                ob = table[index];
                table[index] = value;
                return ob;
            }
            index = (index + (hash | 1)) & (table.length / 2 - 1);
        } while (index != hash);
        // cannot happen; if the table is filled with DELETED entries,
        // we would have found a place for insertion
        rehash();
        return insert(key, value);
    }

    public final Object remove(Object key) {
        if (key == null) {
            throw new IllegalArgumentException("Null key");
        }
        int hash = (-1640531527 * hashCode(key)) >>> ld;
        int index = hash;
        do {
            Object ob = table[index];
            if (ob == null) {
                return null;
            }
            if (equals(ob, key)) {
                table[index] = DELETED;
                index += table.length / 2;
                ob = table[index];
                table[index] = null;
                count -= 1;
                return ob;
            }
            index = (index + (hash | 1)) & (table.length / 2 - 1);
        } while (index != hash);
        return null;
    }

    public void clear() {
        for (int index = table.length; --index >= 0; table[index] = null)
            ;
        count = 0;
    }

    public final Enumeration keys() {
        return new Enumerator(table, true);
    }

    public final Enumeration elements() {
        return new Enumerator(table, false);
    }

    static class Enumerator implements Enumeration {
        int index;

        int stop;

        Object table[];

        Enumerator(Object[] table, boolean keys) {
            this.table = table;
            this.stop = keys ? (table.length / 2) : table.length;
            this.index = keys ? 0 : (table.length / 2);
        }

        public boolean hasMoreElements() {
            while (index < stop) {
                if (table[index] != null && table[index] != DELETED) {
                    return true;
                }
                index += 1;
            }
            return false;
        }

        public Object nextElement() {
            while (index < stop) {
                if (table[index] != null && table[index] != DELETED) {
                    return table[index++];
                }
                index += 1;
            }
            throw new NoSuchElementException("Enumerator");
        }
    }

    public String toString() {
        int max = size() - 1;
        StringBuffer buf = new StringBuffer();
        Enumeration k = keys();
        Enumeration e = elements();
        buf.append("{");
        for (int i = 0; i <= max; i++) {
            String s1 = k.nextElement().toString();
            String s2 = e.nextElement().toString();
            buf.append(s1 + "=" + s2);
            if (i < max) {
                buf.append(", ");
            }
        }
        buf.append("}");
        return buf.toString();
    }

}

