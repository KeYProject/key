package java.util;

public interface SortedSet extends Set
{
  Comparator comparator();

  Object first();

  SortedSet headSet(Object toElement);

  Object last();

  SortedSet subSet(Object fromElement, Object toElement);
  SortedSet tailSet(Object fromElement);
}
