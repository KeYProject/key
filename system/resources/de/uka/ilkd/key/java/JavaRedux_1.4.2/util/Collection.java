package java.util;
public interface Collection
{

    //@ public model instance non_null JMLEqualsBag theCollection;

    //@ instance ghost public \TYPE elementType;

    //@ public instance invariant elementType == theCollection.elementType; 
    //@ instance ghost public boolean containsNull;
    //@ public instance invariant containsNull == theCollection.containsNull;

    //@ public instance ghost Object[] list;
    //@ public instance ghost int end;
    //@ public invariant (\forall int i; list.length > i) && end >= 0;

    /*@
      @   public normal_behavior
      @     assignable end, list[end];
      @     ensures \old(end)+1 == end;
      @     ensures list[end-1] == o; 
      @*/
  boolean add(Object o);

  boolean addAll(Collection c);

    /*@ public behavior
      @   assignable theCollection;
      @   ensures theCollection.isEmpty();
      @   ensures_redundantly size() == 0;
      @   signals (UnsupportedOperationException);
      @ also 
      @  public normal_behavior
      @   assignable end;
      @   ensures end == 0;
      @*/
  void clear();

    /*@ public normal_behavior
      @  ensures \result <==> (\exists int i; i>=0 && i<end; 
      @                        o==null ? list[i]==null : o.equals(list[i]));
      @*/
  boolean contains(Object o);

    /*@ public normal_behavior
      @  ensures \result <==> (\forall int j; j>=0 && j<c.end;
      @                          (\exists int i; i>=0 && i<end; 
      @                           c.list[j]==null ? 
      @                           list[i]==null : c.list[j].equals(list[i])));
      @*/
  boolean containsAll(Collection c);

  boolean equals(Object o);

  int hashCode();

    /*@ public normal_behavior
      @   ensures \result <==> (end == 0); 
      @*/
  boolean isEmpty();

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result != null;
      @   ensures \result.elementType == elementType;
      @   ensures containsNull == \result.returnsNull;
      @   ensures (\forall int i; 0 <= i && i < size();
      @                 theCollection.has(\result.nthNextElement(i)));
      @   ensures (\forall Object o; theCollection.has(o) ==>
      @              (\exists int i; 0 <= i && i < size(); 
      @                 o == \result.nthNextElement(i)));
      @   ensures size() > 0 ==> \result.hasNext((int)(size()-1));
      @   ensures !\result.hasNext((int)(size()));
      @   ensures_redundantly
      @           (\forall int i; 0 <= i && i < size();
      @                 this.contains(\result.nthNextElement(i)));
      @   ensures_redundantly size() != 0 ==> \result.moreElements;
      @*/
  Iterator iterator();

    /*@ public behavior
      @   requires !containsNull ==> o != null;
      @   requires  (o == null) || \typeof(o) <: elementType;
      @   assignable theCollection;
      @   ensures \result
      @         ==> theCollection.equals(\old(theCollection.remove(o)));
      @   ensures \result && \old(size() <= Integer.MAX_VALUE)
      @           ==> size() == \old(size()-1) && size() < Integer.MAX_VALUE
      @               && size() >= 0;
      @   ensures !\result || \old(size() == Integer.MAX_VALUE)
      @           ==> size() == \old(size());
      @   signals (UnsupportedOperationException);
      @   signals (ClassCastException);
      @*/
  boolean remove(Object o);

  boolean removeAll(Collection c);

  boolean retainAll(Collection c);

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == theCollection.int_size();
      @
      @ also normal_behavior
      @    ensures \result >= 0;
      @ also normal_behavior
      @    ensures \result == end;
      @*/
  int size();

    /*@ public normal_behavior
      @  ensures \result.length == end && (\forall int i; i>=0 && i<end; 
      @                                    list[i] == \result[i]);
      @*/
  Object[] toArray();

  Object[] toArray(Object[] a);
}
