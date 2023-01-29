// This file is part of the RECODER library and protected by the LGPL.

package recoder.util;

import java.util.Enumeration;
import java.util.NoSuchElementException;

/**
 * @author AL
 */
public abstract class AbstractIndex implements HashCode {

    Object table[];

    long id[];

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

    public AbstractIndex() {
        this(4);
    }

    public AbstractIndex(int initialCapacity) {
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
        id = new long[cap];
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
        long[] oldId = id;
        int oldCapacity = oldMap.length;
        ld -= 1;
        table = new Object[oldCapacity * 2];
        id = new long[oldCapacity * 2];
        count = 0;
        for (int i = oldCapacity - 1; i >= 0; i -= 1) {
            Object ob = oldMap[i];
            if (ob != null && ob != DELETED) {
                insert(ob, oldId[i]);
            }
        }
    }

    public boolean contains(Object key) {
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
            index = (index + (hash | 1)) & (table.length - 1);
        } while (index != hash);
        return false;
    }

    public final long get(Object key) {
        if (key == null) {
            return -1L;
        }
        int hash = (-1640531527 * hashCode(key)) >>> ld;
        int index = hash;
        do {
            Object ob = table[index];
            if (ob == null) {
                return -1L;
            }
            if (equals(ob, key)) {
                return id[index];
            }
            index = (index + (hash | 1)) & (table.length - 1);
        } while (index != hash);
        return -1;
    }

    public final long put(Object key, long id) {
        if (key == null) {
            throw new IllegalArgumentException("Null key");
        }
        if (count >= table.length * THRESHOLD) {
            rehash();
        }
        return insert(key, id);
    }

    private long insert(Object key, long id) {
        int hash = (-1640531527 * hashCode(key)) >>> ld;
        int index = hash;
        do {
            Object ob = table[index];
            if (ob == null || ob == DELETED) {
                table[index] = key;
                this.id[index] = id;
                count += 1;
                return -1L;
            }
            if (equals(ob, key)) {
                long i = this.id[index];
                table[index] = key;
                this.id[index] = id;
                return i;
            }
            index = (index + (hash | 1)) & (table.length - 1);
        } while (index != hash);
        // should never happen
        rehash();
        return insert(key, id);
    }

    public final long remove(Object key) {
        if (key == null) {
            throw new IllegalArgumentException("Null key");
        }
        int hash = (-1640531527 * hashCode(key)) >>> ld;
        int index = hash;
        do {
            Object ob = table[index];
            if (ob == null) {
                return -1L;
            }
            if (equals(ob, key)) {
                table[index] = DELETED;
                count -= 1;
                return id[index];
            }
            index = (index + (hash | 1)) & (table.length - 1);
        } while (index != hash);
        return -1L;
    }

    public void clear() {
        for (int index = table.length; --index >= 0; table[index] = null)
            ;
        count = 0;
    }

    public final Enumeration elements() {
        return new Enumerator(table);
    }

    static class Enumerator implements Enumeration {
        int index;

        Object table[];

        Enumerator(Object[] table) {
            this.table = table;
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
        if (!(ob instanceof AbstractIndex)) {
            return false;
        }
        AbstractIndex x = (AbstractIndex) ob;
        if (x.size() != size()) {
            return false;
        }
        Enumeration enum2 = x.elements();
        while (enum2.hasMoreElements()) {
            Object z = enum2.nextElement();
            if (get(z) != x.get(z)) {
                return false;
            }
        }
        return true;
    }

    public Object clone() {
        try {
            AbstractIndex t = (AbstractIndex) super.clone();
            t.table = new Object[table.length];
            for (int i = table.length; i-- > 0;) {
                t.table[i] = table[i];
                t.id[i] = id[i];
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
            buf.append("=");
            buf.append(get(s));
            if (i < max) {
                buf.append(", ");
            }
        }
        buf.append("}");
        return buf.toString();
    }
}