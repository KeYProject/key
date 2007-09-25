package java.util;

public interface Set extends Collection
{
  boolean add(Object o);

  boolean addAll(Collection c);

  void clear();

  boolean contains(Object o);

  boolean containsAll(Collection c);

  boolean equals(Object o);

  int hashCode();

  boolean isEmpty();

  Iterator iterator();

  boolean remove(Object o);

  boolean removeAll(Collection c);

  boolean retainAll(Collection c);

  int size();

  Object[] toArray();

  Object[] toArray(Object[] a);
}
