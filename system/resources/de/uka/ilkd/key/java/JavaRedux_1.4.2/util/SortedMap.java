package java.util;
public interface SortedMap extends Map
{
  Comparator comparator();

  Object firstKey();

  SortedMap headMap(Object toKey);

  Object lastKey();

  SortedMap subMap(Object fromKey, Object toKey);

  SortedMap tailMap(Object fromKey);
}
