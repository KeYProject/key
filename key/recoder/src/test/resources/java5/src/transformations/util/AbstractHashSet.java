// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

import java.util.Enumeration;
import java.util.NoSuchElementException;

/**
 * @author AL
 */
public abstract class AbstractHashSet implements MutableSet, HashCode {

    Object table[];

    int count;

    int ld;

    // sweeping position, to guarantee amortized O(1) for removeAny operations
    int sweep;

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

    public AbstractHashSet() {
    }

    public AbstractHashSet(int initialCapacity) {
        init(initialCapacity);
    }

    private void init(int initialCapacity) {
        if (initialCapacity < 4) {
            initialCapacity = 4;
        }
        int cap = 4;
        ld = 2;
        while (cap < initialCapacity) {
            ld += 1;
            cap += cap;
        }
        table = new Object[cap];
        ld = 32 - ld;
        sweep = 0;
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
        for (int i = oldCapacity - 1; i >= 0; i -= 1) {
            Object ob = oldMap[i];
            if (ob != null && ob != DELETED) {
                insert(ob);
            }
        }
        sweep = 0;
    }

    public boolean contains(Object key) {
        return get(key) != null;
    }

    public final Object get(Object key) {
        if (key == null || isEmpty()) {
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
                return ob;
            }
            index = (index + (hash | 1)) & (table.length - 1);
        } while (index != hash);
        return null;
    }

    public final Object add(Object key) {
        if (key == null) {
            throw new IllegalArgumentException("Null key");
        }
        if (table == null) {
            init(1);
        } else if (count >= table.length * THRESHOLD) {
            rehash();
        }
        return insert(key);
    }

    private Object insert(Object key) {
        int hash = (-1640531527 * hashCode(key)) >>> ld;
        int index = hash;
        do {
            Object ob = table[index];
            if (ob == null || ob == DELETED) {
                table[index] = key;
                count += 1;
                return null;
            }
            if (equals(ob, key)) {
                table[index] = key;
                return ob;
            }
            index = (index + (hash | 1)) & (table.length - 1);
        } while (index != hash);
        // should never happen
        rehash();
        return insert(key);
    }

    public final Object remove(Object key) {
        if (key == null) {
            throw new IllegalArgumentException("Null key");
        }
        if (!isEmpty()) {
            int hash = (-1640531527 * hashCode(key)) >>> ld;
            int index = hash;
            do {
                Object ob = table[index];
                if (ob == null) {
                    return null;
                }
                if (equals(ob, key)) {
                    table[index] = DELETED;
                    count -= 1;
                    return ob;
                }
                index = (index + (hash | 1)) & (table.length - 1);
            } while (index != hash);
        }
        return null;
    }

    public Object removeAny() {
        if (isEmpty()) {
            return null;
        }
        while (true) {
            if (sweep > table.length) {
                sweep = 0;
            }
            Object ob = table[sweep];
            if (ob != null && ob != DELETED) {
                table[sweep] = DELETED;
                count -= 1;
                return ob;
            }
            sweep += 1;
        }
    }

    public void clear() {
        table = null;
        count = 0;
    }

    public final Enumeration elements() {
        return new Enumerator(table);
    }

    static class Enumerator implements Enumeration {
        int index;

        Object table[];

        Enumerator(Object[] table) {
            this.table = table != null ? table : new Object[0];
            this.index = 0;
        }

        public boolean hasMoreElements() {
            while (index < table.length) {
                if (table[index] != null && table[index] != DELETED) {
                    return true;
                }
                index += 1;
            }
            return false;
        }

        public Object nextElement() {
            while (index < table.length) {
                if (table[index] != null && table[index] != DELETED) {
                    return table[index++];
                }
                index += 1;
            }
            throw new NoSuchElementException("Enumerator");
        }
    }

    public boolean equals(Object ob) {
        if (!(ob instanceof Set)) {
            return false;
        }
        Set x = (Set) ob;
        if (x.size() != size()) {
            return false;
        }
        Enumeration enum2 = x.elements();
        while (enum2.hasMoreElements()) {
            if (!contains(enum2.nextElement())) {
                return false;
            }
        }
        return true;
    }

    public void join(Set set) {
        Debug.assertNonnull(set);
        Enumeration enum2 = set.elements();
        while (enum2.hasMoreElements()) {
            add(enum2.nextElement());
        }
    }

    public void intersect(Set set) {
        Debug.assertNonnull(set);
        Enumeration enum2 = elements();
        for (int i = size() - 1; i >= 0; i -= 1) {
            Object el = enum2.nextElement();
            if (!set.contains(el)) {
                remove(el);
            }
        }
    }

    public void subtract(Set set) {
        Debug.assertNonnull(set);
        Enumeration enum2 = set.elements();
        while (enum2.hasMoreElements()) {
            remove(enum2.nextElement());
        }
    }

    public Object clone() {
        try {
            AbstractHashSet t = (AbstractHashSet) super.clone();
            if (table != null) {
                t.table = new Object[table.length];
                for (int i = table.length; i-- > 0;) {
                    t.table[i] = table[i];
                }
            }
            return t;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }

    public String toString() {
        int max = size() - 1;
        StringBuffer buf = new StringBuffer();
        Enumeration e = elements();
        buf.append("{");
        for (int i = 0; i <= max; i++) {
            String s = e.nextElement().toString();
            buf.append(s);
            if (i < max) {
                buf.append(", ");
            }
        }
        buf.append("}");
        return buf.toString();
    }
}