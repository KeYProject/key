package java.util;

public interface ListIterator extends Iterator
{
  boolean hasNext();

  boolean hasPrevious();

  Object next();

  Object previous();

  int nextIndex();

  int previousIndex();

  void add(Object o);

  void remove();

  void set(Object o);
}
