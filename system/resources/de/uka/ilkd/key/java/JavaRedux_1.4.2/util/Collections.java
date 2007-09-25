


package java.util;

import java.io.Serializable;
public class Collections {
    private static boolean isSequential(List l) {}
    private Collections() {}
    public static final Set EMPTY_SET = new EmptySet();
    private static final class EmptySet extends AbstractSet
     implements Serializable {
        EmptySet() {}
        public int size() {}
        public Iterator iterator() {}
        public boolean contains(Object o) {}
        public boolean containsAll(Collection c) {}
        public boolean equals(Object o) {}
        public int hashCode() {}
        public boolean remove(Object o) {}
        public boolean removeAll(Collection c) {}
        public boolean retainAll(Collection c) {}
        public Object[] toArray() {}
        public Object[] toArray(Object[] a) {}
        public String toString() {}
    }
    public static final List EMPTY_LIST = new EmptyList();
    private static final class EmptyList extends AbstractList
     implements Serializable, RandomAccess {
        EmptyList() {}
        public int size() {}
        public Object get(int index) {}
        public boolean contains(Object o) {}
        public boolean containsAll(Collection c) {}
        public boolean equals(Object o) {}
        public int hashCode() {}
        public int indexOf(Object o) {}
        public int lastIndexOf(Object o) {}
        public boolean remove(Object o) {}
        public boolean removeAll(Collection c) {}
        public boolean retainAll(Collection c) {}
        public Object[] toArray() {}
        public Object[] toArray(Object[] a) {}
        public String toString() {}
    }
    public static final Map EMPTY_MAP = new EmptyMap();
    private static final class EmptyMap extends AbstractMap
     implements Serializable {
        EmptyMap() {}
        public Set entrySet() {}
        public boolean containsKey(Object key) {}
        public boolean containsValue(Object value) {}
        public boolean equals(Object o) {}
        public Object get(Object o) {}
        public int hashCode() {}
        public Set keySet() {}
        public Object remove(Object o) {}
        public int size() {}
        public Collection values() {}
        public String toString() {}
    }
    static final int compare(Object o1, Object o2, Comparator c) {}
    public static int binarySearch(List l, Object key) {}
    public static int binarySearch(List l, Object key, Comparator c) {}
    public static void copy(List dest, List source) {}
    public static Enumeration enumeration(Collection c) {}
    public static void fill(List l, Object val) {}
    public static int indexOfSubList(List source, List target) {}
    public static int lastIndexOfSubList(List source, List target) {}
    public static ArrayList list(Enumeration e) {}
    public static Object max(Collection c) {}
    public static Object max(Collection c, Comparator order) {}
    public static Object min(Collection c) {}
    public static Object min(Collection c, Comparator order) {}
    public static List nCopies(final int n, final Object o) {}
    private static final class CopiesList extends AbstractList
     implements Serializable, RandomAccess {
        CopiesList(int n, Object o) {}
        public int size() {}
        public Object get(int index) {}
        public boolean contains(Object o) {}
        public int indexOf(Object o) {}
        public int lastIndexOf(Object o) {}
        public List subList(int from, int to) {}
        public Object[] toArray() {}
        public String toString() {}
    }
    public static boolean replaceAll(List list, Object oldval, Object newval) {}
    public static void reverse(List l) {}
    public static Comparator reverseOrder() {}
    private static final class ReverseComparator
     implements Comparator, Serializable {
        ReverseComparator() {}
        public int compare(Object a, Object b) {}
    }
    public static void rotate(List list, int distance) {}
    public static void shuffle(List l) {}
    public static void shuffle(List l, Random r) {}
    public static Set singleton(Object o) {}
    private static final class SingletonSet extends AbstractSet
     implements Serializable {
        final Object element;
        SingletonSet(Object o) {}
        public int size() {}
        public Iterator iterator() {}
        public boolean contains(Object o) {}
        public boolean containsAll(Collection c) {}
        public int hashCode() {}
        public Object[] toArray() {}
        public String toString() {}
    }
    public static List singletonList(Object o) {}
    private static final class SingletonList extends AbstractList
     implements Serializable, RandomAccess {
        SingletonList(Object o) {}
        public int size() {}
        public Object get(int index) {}
        public boolean contains(Object o) {}
        public boolean containsAll(Collection c) {}
        public int hashCode() {}
        public int indexOf(Object o) {}
        public int lastIndexOf(Object o) {}
        public List subList(int from, int to) {}
        public Object[] toArray() {}
        public String toString() {}
    }
    public static Map singletonMap(Object key, Object value) {}
    private static final class SingletonMap extends AbstractMap
     implements Serializable {
        SingletonMap(Object key, Object value) {}
        public Set entrySet() {}
        public boolean containsKey(Object key) {}
        public boolean containsValue(Object value) {}
        public Object get(Object key) {}
        public int hashCode() {}
        public Set keySet() {}
        public int size() {}
        public Collection values() {}
        public String toString() {}
    }
    public static void sort(List l) {}
    public static void sort(List l, Comparator c) {}
    public static void swap(List l, int i, int j) {}
    public static Collection synchronizedCollection(Collection c) {}
    static class SynchronizedCollection
     implements Collection, Serializable {
        final Collection c;
        final Object mutex;
        SynchronizedCollection(Collection c) {}
        SynchronizedCollection(Object sync, Collection c) {}

        public boolean add(Object o) {}

        public boolean addAll(Collection col) {}

        public void clear() {}

        public boolean contains(Object o) {}

        public boolean containsAll(Collection c1) {}

        public boolean isEmpty() {}

        public Iterator iterator() {}

        public boolean remove(Object o) {}

        public boolean removeAll(Collection col) {}

        public boolean retainAll(Collection col) {}

        public int size() {}

        public Object[] toArray() {}

        public Object[] toArray(Object[] a) {}

        public String toString() {}
    }
    private static class SynchronizedIterator implements Iterator {
        final Object mutex;
        SynchronizedIterator(Object sync, Iterator i) {}

        public Object next() {}

        public boolean hasNext() {}

        public void remove() {}
    }
    public static List synchronizedList(List l) {}
    static class SynchronizedList extends SynchronizedCollection
     implements List {
        final List list;
        SynchronizedList(List l) {}
        SynchronizedList(Object sync, List l) {}

        public void add(int index, Object o) {}

        public boolean addAll(int index, Collection c) {}

        public boolean equals(Object o) {}

        public Object get(int index) {}

        public int hashCode() {}

        public int indexOf(Object o) {}

        public int lastIndexOf(Object o) {}

        public ListIterator listIterator() {}

        public ListIterator listIterator(int index) {}

        public Object remove(int index) {}

        public Object set(int index, Object o) {}

        public List subList(int fromIndex, int toIndex) {}
    }
    private static final class SynchronizedRandomAccessList
     extends SynchronizedList implements RandomAccess {
        SynchronizedRandomAccessList(List l) {}
        SynchronizedRandomAccessList(Object sync, List l) {}

        public List subList(int fromIndex, int toIndex) {}
    }
    private static final class SynchronizedListIterator
     extends SynchronizedIterator implements ListIterator {
        SynchronizedListIterator(Object sync, ListIterator li) {}

        public void add(Object o) {}
        public boolean hasPrevious() {}

        public int nextIndex() {}

        public Object previous() {}

        public int previousIndex() {}

        public void set(Object o) {}
    }
    public static Map synchronizedMap(Map m) {}
    private static class SynchronizedMap implements Map, Serializable {
        final Object mutex;
        SynchronizedMap(Map m) {}
        SynchronizedMap(Object sync, Map m) {}

        public void clear() {}

        public boolean containsKey(Object key) {}

        public boolean containsValue(Object value) {}
        public Set entrySet() {}

        public boolean equals(Object o) {}

        public Object get(Object key) {}

        public int hashCode() {}

        public boolean isEmpty() {}

        public Set keySet() {}

        public Object put(Object key, Object value) {}

        public void putAll(Map map) {}

        public Object remove(Object o) {}

        public int size() {}

        public String toString() {}

        public Collection values() {}
    }
    public static Set synchronizedSet(Set s) {}
    static class SynchronizedSet extends SynchronizedCollection
     implements Set {
        SynchronizedSet(Set s) {}
        SynchronizedSet(Object sync, Set s) {}

        public boolean equals(Object o) {}

        public int hashCode() {}
    }
    public static SortedMap synchronizedSortedMap(SortedMap m) {}
    private static final class SynchronizedSortedMap extends SynchronizedMap
     implements SortedMap {
        SynchronizedSortedMap(SortedMap sm) {}
        SynchronizedSortedMap(Object sync, SortedMap sm) {}

        public Comparator comparator() {}

        public Object firstKey() {}

        public SortedMap headMap(Object toKey) {}

        public Object lastKey() {}

        public SortedMap subMap(Object fromKey, Object toKey) {}

        public SortedMap tailMap(Object fromKey) {}
    }
    public static SortedSet synchronizedSortedSet(SortedSet s) {}
    private static final class SynchronizedSortedSet extends SynchronizedSet
     implements SortedSet {
        SynchronizedSortedSet(SortedSet ss) {}
        SynchronizedSortedSet(Object sync, SortedSet ss) {}

        public Comparator comparator() {}

        public Object first() {}

        public SortedSet headSet(Object toElement) {}

        public Object last() {}

        public SortedSet subSet(Object fromElement, Object toElement) {}

        public SortedSet tailSet(Object fromElement) {}
    }
    public static Collection unmodifiableCollection(Collection c) {}
    private static class UnmodifiableCollection
     implements Collection, Serializable {
        final Collection c;
        UnmodifiableCollection(Collection c) {}

        public boolean add(Object o) {}

        public boolean addAll(Collection c) {}

        public void clear() {}

        public boolean contains(Object o) {}

        public boolean containsAll(Collection c1) {}

        public boolean isEmpty() {}

        public Iterator iterator() {}

        public boolean remove(Object o) {}

        public boolean removeAll(Collection c) {}

        public boolean retainAll(Collection c) {}

        public int size() {}

        public Object[] toArray() {}

        public Object[] toArray(Object[] a) {}

        public String toString() {}
    }
    private static class UnmodifiableIterator implements Iterator {
        UnmodifiableIterator(Iterator i) {}

        public Object next() {}

        public boolean hasNext() {}

        public void remove() {}
    }
    public static List unmodifiableList(List l) {}
    private static class UnmodifiableList extends UnmodifiableCollection
     implements List {
        final List list;
        UnmodifiableList(List l) {}

        public void add(int index, Object o) {}

        public boolean addAll(int index, Collection c) {}

        public boolean equals(Object o) {}

        public Object get(int index) {}

        public int hashCode() {}

        public int indexOf(Object o) {}

        public int lastIndexOf(Object o) {}

        public ListIterator listIterator() {}

        public ListIterator listIterator(int index) {}

        public Object remove(int index) {}

        public Object set(int index, Object o) {}

        public List subList(int fromIndex, int toIndex) {}
    }
    private static final class UnmodifiableRandomAccessList
     extends UnmodifiableList implements RandomAccess {
        UnmodifiableRandomAccessList(List l) {}
    }
    private static final class UnmodifiableListIterator
     extends UnmodifiableIterator implements ListIterator {
        UnmodifiableListIterator(ListIterator li) {}

        public void add(Object o) {}

        public boolean hasPrevious() {}

        public int nextIndex() {}

        public Object previous() {}

        public int previousIndex() {}

        public void set(Object o) {}
    }
    public static Map unmodifiableMap(Map m) {}
    private static class UnmodifiableMap implements Map, Serializable {
        UnmodifiableMap(Map m) {}

        public void clear() {}

        public boolean containsKey(Object key) {}

        public boolean containsValue(Object value) {}

        public Set entrySet() {}
        private static final class UnmodifiableEntrySet extends UnmodifiableSet
         implements Serializable {
            UnmodifiableEntrySet(Set s) {}
            public Iterator iterator() {}
        }

        public boolean equals(Object o) {}

        public Object get(Object key) {}

        public Object put(Object key, Object value) {}

        public int hashCode() {}

        public boolean isEmpty() {}

        public Set keySet() {}

        public void putAll(Map m) {}

        public Object remove(Object o) {}

        public int size() {}

        public String toString() {}

        public Collection values() {}
    }
    public static Set unmodifiableSet(Set s) {}
    private static class UnmodifiableSet extends UnmodifiableCollection
     implements Set {
        UnmodifiableSet(Set s) {}

        public boolean equals(Object o) {}

        public int hashCode() {}
    }
    public static SortedMap unmodifiableSortedMap(SortedMap m) {}
    private static class UnmodifiableSortedMap extends UnmodifiableMap
     implements SortedMap {
        UnmodifiableSortedMap(SortedMap sm) {}

        public Comparator comparator() {}

        public Object firstKey() {}

        public SortedMap headMap(Object toKey) {}

        public Object lastKey() {}

        public SortedMap subMap(Object fromKey, Object toKey) {}

        public SortedMap tailMap(Object fromKey) {}
    }
    public static SortedSet unmodifiableSortedSet(SortedSet s) {}
    private static class UnmodifiableSortedSet extends UnmodifiableSet
     implements SortedSet {
        UnmodifiableSortedSet(SortedSet ss) {}

        public Comparator comparator() {}

        public Object first() {}

        public SortedSet headSet(Object toElement) {}

        public Object last() {}

        public SortedSet subSet(Object fromElement, Object toElement) {}

        public SortedSet tailSet(Object fromElement) {}
    }
}
