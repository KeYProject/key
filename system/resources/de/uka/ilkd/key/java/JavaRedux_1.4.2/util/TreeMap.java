


package java.util;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
public class TreeMap extends AbstractMap
  implements SortedMap, Cloneable, Serializable {
    static final int RED = -1,
                   BLACK = 1;
    static final Node nil = new Node(null, null, BLACK);
    static {}
    transient int size;
    transient int modCount;
    final Comparator comparator;
    private static final class Node extends AbstractMap.BasicMapEntry {
        int color;
        Node left = nil;
        Node right = nil;
        Node parent = nil;
        Node(Object key, Object value, int color) {}
    }
    public TreeMap() {}
    public TreeMap(Comparator c) {}
    public TreeMap(Map map) {}
    public TreeMap(SortedMap sm) {}
    public void clear() {}
    public Object clone() {}
    public Comparator comparator() {}
    public boolean containsKey(Object key) {}
    public boolean containsValue(Object value) {}
    public Set entrySet() {}
    public Object firstKey() {}
    public Object get(Object key) {}
    public SortedMap headMap(Object toKey) {}
    public Set keySet() {}
    public Object lastKey() {}
    public Object put(Object key, Object value) {}
    public void putAll(Map m) {}
    public Object remove(Object key) {}
    public int size() {}
    public SortedMap subMap(Object fromKey, Object toKey) {}
    public SortedMap tailMap(Object fromKey) {}
    public Collection values() {}
    final int compare(Object o1, Object o2) {}
    private void deleteFixup(Node node, Node parent) {}
    private void fabricateTree(final int count) {}
    final Node firstNode() {}
    final Node getNode(Object key) {}
    final Node highestLessThan(Object key) {}
    private void insertFixup(Node n) {}
    private Node lastNode() {}
    final Node lowestGreaterThan(Object key, boolean first) {}
    private Node predecessor(Node node) {}
    final void putFromObjStream(ObjectInputStream s, int count,
                              boolean readValues)
     throws IOException, ClassNotFoundException {}
    final void putKeysLinear(Iterator keys, int count) {}
    private void readObject(ObjectInputStream s)
     throws IOException, ClassNotFoundException {}
    final void removeNode(Node node) {}
    private void rotateLeft(Node node) {}
    private void rotateRight(Node node) {}
    final Node successor(Node node) {}
    private void writeObject(ObjectOutputStream s) throws IOException {}
    private final class TreeIterator implements Iterator {
        TreeIterator(int type) {}
        TreeIterator(int type, Node first, Node max) {}
        public boolean hasNext() {}
        public Object next() {}
        public void remove() {}
    }
    private final class SubMap extends AbstractMap implements SortedMap {
        final Object minKey;
        final Object maxKey;
        SubMap(Object minKey, Object maxKey) {}
        final boolean keyInRange(Object key) {}

        public void clear() {}

        public Comparator comparator() {}

        public boolean containsKey(Object key) {}

        public boolean containsValue(Object value) {}

        public Set entrySet() {}

        public Object firstKey() {}

        public Object get(Object key) {}

        public SortedMap headMap(Object toKey) {}

        public Set keySet() {}

        public Object lastKey() {}

        public Object put(Object key, Object value) {}

        public Object remove(Object key) {}

        public int size() {}

        public SortedMap subMap(Object fromKey, Object toKey) {}

        public SortedMap tailMap(Object fromKey) {}

        public Collection values() {}
    }
}
