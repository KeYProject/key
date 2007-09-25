package java.util;
public interface List extends Collection
{

    /*@ public model instance non_null JMLEqualsSequence theList;
      @                                               in theCollection;
      @ public instance represents theCollection <- theList.toBag();
      @*/

    /*@
      @   public normal_behavior
      @     requires index <= end; 
      @     assignable end, list[end];
      @     ensures \old(end)+1 == end;
      @     ensures list[index] == o; 
      @     ensures (\forall int i; i>=index && i<end-1; \old(list[i]) == list[i+1]);
      @*/
  void add(int index, Object o);

    /*@ also
      @   public behavior
      @     assignable theCollection;
      @     ensures \result ==> theList.equals(\old(theList).insertBack(o));
      @*/
  boolean add(Object o);

    /*@   public behavior
      @     requires c != null;
      @     requires 0 <= index && index <= size();
      @     requires c.elementType <: elementType;
      @     requires !containsNull ==> !c.containsNull;
      @     assignable theCollection;
      @     ensures \result
      @         ==> theList.equals(
      @                     \old(theList.subsequence(0,index))
      @                      .concat(JMLEqualsSequence.convertFrom(c))
      @                      .concat(\old(theList.subsequence(index,size()))));
      @     signals (UnsupportedOperationException);
      @     signals (IllegalArgumentException);
      @ also
      @   public exceptional_behavior
      @     requires c == null || !(0 <= index && index <= size())
      @             || !(c.elementType <: elementType)
      @             || (!containsNull && c.containsNull);
      @     assignable \nothing;
      @     signals (ClassCastException)
      @             c != null && !(c.elementType <: elementType);
      @     signals (NullPointerException) c == null;
      @     signals (IndexOutOfBoundsException)
      @             !(0 <= index && index <= size());
      @*/
  boolean addAll(int index, Collection c);

  boolean addAll(Collection c);

  void clear();

  boolean contains(Object o);

    //@ pure
  boolean containsAll(Collection c);

  boolean equals(Object o);

    /*@ public normal_behavior
      @   requires 0 <= index && index < size();
      @   assignable \nothing;
      @   ensures \result == theList.get(index);
      @ also
      @ public normal_behavior
      @   requires 0 <= index && index < size();
      @   assignable \nothing;
      @   ensures \result == list[index];
      @ also
      @ public exceptional_behavior
      @   requires !(0 <= index && index < size());
      @   assignable \nothing;
      @   signals (IndexOutOfBoundsException);
      @*/
    //@ pure 
  Object get(int index);

  int hashCode();

    /*@ public normal_behavior
      @   requires (\exists int i; 0<=i && i<end;  
      @             o == null ? list[i] == o : o.equals(list[i]));
      @   ensures  o == null ? list[\result] == o : o.equals(list[\result]);
      @   ensures  (\forall int j; 0<=j && j<end; o == null ? 
      @             list[j] == o ==> j>=\result : 
      @             o.equals(list[j]) ==> j>=\result);
      @ also public normal_behavior
      @   requires (\forall int i; 0<=i && i<end;  
      @             o == null ? list[i] != o : !o.equals(list[i]));
      @   ensures \result == -1;
      @*/
  int /*@ pure @*/ indexOf(Object o);

  boolean /*@ pure @*/ isEmpty();

    /*@ also
      @ public behavior
      @   assignable \nothing;
      @   ensures \result != null;
      @   ensures size() < Integer.MAX_VALUE
      @       ==> (\forall int i; 0 <= i && i < size();
      @                \result.hasNext(i) && \result.nthNextElement(i)
      @                 == toArray()[i]);
      @*/
  Iterator iterator();

  int lastIndexOf(Object o);

  ListIterator listIterator();

  ListIterator listIterator(int index);

  Object remove(int index);

    /*@ also
      @   public behavior
      @     assignable theCollection;
      @     ensures \result
      @          ==> theList
      @              .equals(\old(theList.removeItemAt(theList.indexOf(o))));
      @*/
  boolean remove(Object o);

  boolean removeAll(Collection c);

  boolean retainAll(Collection c);

    /*@
      @ public behavior
      @ requires !containsNull ==> element != null;
      @ requires (element == null) || \typeof(element) <: elementType;
      @ {|
      @   requires 0 <= index && index < size();
      @   assignable theCollection;
      @   ensures \result == (\old(theList.get(index)));
      @   ensures theList.equals(
      @              \old(theList.subsequence(0,index))
      @                   .insertBack(element)
      @                   .concat(\old(theList.subsequence(index+1,size()))));
      @   signals (UnsupportedOperationException);
      @   signals (ClassCastException);
      @   signals (NullPointerException);
      @   signals (IllegalArgumentException);
      @ also
      @   requires !(0 <= index && index < size());
      @   assignable \nothing;
      @   ensures false;
      @   signals (IndexOutOfBoundsException);
      @ |}
      @*/
  Object set(int index, Object element);

  int /*@ pure @*/ size();

  List subList(int fromIndex, int toIndex);

    /*@ also
      @  public normal_behavior
      @   requires size() < Integer.MAX_VALUE;
      @   assignable \nothing;
      @   ensures \result != null;
      @   ensures \result.length == size();
      @   ensures (\forall int i; 0 <= i && i < size();
      @                 \result[i].equals(theList.get(i)));
      @*/
    //@ pure
  Object[] toArray();

    /*@ also
      @ public normal_behavior
      @   old int colSize = theCollection.int_size();
      @   old int arrSize = a.length;
      @   requires a!= null && colSize < Integer.MAX_VALUE;
      @   requires elementType <: \elemtype(\typeof(a));
      @   requires (\forall Object o; contains(o); \typeof(o) <: \elemtype(\typeof(a)));
      @   {|
      @     requires colSize <= arrSize;
      @     assignable a[*];
      @     ensures \result == a;
      @     ensures (\forall int k; 0 <= k && k < colSize;
      @                  theList.get(k) == \result[k]);
      @     ensures (\forall int i; colSize <= i && i < arrSize;
      @                             \result[i] == null);
      @   also
      @     requires colSize > arrSize;
      @     assignable \nothing;
      @     ensures \fresh(\result) && \result.length == colSize;
      @     ensures (\forall int k; 0 <= k && k < colSize;
      @                             theList.get(k) == \result[k]);
      @   |}
      @*/
  Object[] toArray(Object[] a);
}
