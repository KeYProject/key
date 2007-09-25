

package java.util;
import java.io.Serializable;
public class BitSet implements Cloneable, Serializable {
    public BitSet() {}
    public BitSet(int nbits) {}
    public void and(BitSet bs) {}
    public void andNot(BitSet bs) {}
    public int cardinality() {}
    public void clear() {}
    public void clear(int pos) {}
    public void clear(int from, int to) {}
    public Object clone() {}
    public boolean equals(Object obj) {}
    public void flip(int index) {}
    public void flip(int from, int to) {}
    public boolean get(int pos) {}
    public BitSet get(int from, int to) {}
    public int hashCode() {}
    public boolean intersects(BitSet set) {}
    public boolean isEmpty() {}
    public int length() {}
    public int nextClearBit(int from) {}
    public int nextSetBit(int from) {}
    public void or(BitSet bs) {}
    public void set(int pos) {}
    public void set(int index, boolean value) {}
    public void set(int from, int to) {}
    public void set(int from, int to, boolean value) {}
    public int size() {}
    public String toString() {}
    public void xor(BitSet bs) {}
    private final void ensure(int lastElt) {}
}
