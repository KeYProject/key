


package java.util;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.lang.reflect.Array;
public class ArrayList extends AbstractList
  implements List, RandomAccess, Cloneable, Serializable {

    /*@ public model int capacity;
      @*/

    /*@  public normal_behavior
      @   requires 0 <= initialCapacity;
      @   assignable capacity, theCollection;
      @   ensures capacity == initialCapacity;
      @   ensures this.isEmpty();
      @ also
      @  public exceptional_behavior
      @   requires initialCapacity < 0;
      @   assignable \nothing;
      @   signals (IllegalArgumentException) initialCapacity < 0;
      @*/
    public ArrayList(int initialCapacity) {}

    /*@  public normal_behavior
      @   assignable capacity, theCollection;
      @   ensures capacity == 10;
      @   ensures this.isEmpty();
      @*/
    public ArrayList() {}

    /*@  public normal_behavior
      @   requires c != null;
      @   requires c.size()*2 <= Integer.MAX_VALUE;
      @   assignable capacity, theCollection;
      @   ensures this.size() == c.size();
      @   ensures (\forall int i; 0 <= i && i < c.size();
      @                     this.get(i).equals(c.iterator().nthNextElement(i)));
      @   ensures_redundantly c.theCollection.equals(this.theCollection);
      @   ensures capacity == c.size();
      @ also
      @  public exceptional_behavior
      @   requires c == null;
      @   assignable \nothing;
      @   signals (NullPointerException) c == null;
      @*/
    public ArrayList(Collection c) {}

    /*@  public normal_behavior
      @   assignable capacity, theCollection;
      @   ensures capacity == this.size();
      @*/
    public void trimToSize() {}
    public void ensureCapacity(int minCapacity) {}
    public int size() {}
    public boolean isEmpty() {}
    public boolean contains(Object e) {}
    public int indexOf(Object e) {}
    public int lastIndexOf(Object e) {}

   /*@ also
      @ implies_that
      @  public normal_behavior
      @   assignable \nothing;
      @   ensures \result != this;
      @   ensures \result.getClass() == this.getClass();
      @   ensures \result.equals(this);
      @   ensures \result != null;
      @   ensures ((ArrayList)\result).size() == this.size();
      @   ensures (\forall int i; 0 <= i && i < this.size();
      @             ((ArrayList)\result).get(i) == this.get(i));
      @*/
    public Object clone() {}

    public Object[] toArray() {}

    /*@ also
      @  public exceptional_behavior
      @   requires elementType <: \elemtype(\typeof(a));
      @   assignable \nothing;
      @   signals (ArrayStoreException);
      @*/
    public Object[] toArray(Object[] a) {}
    public Object get(int index) {}

    /*@ also
      @  public exceptional_behavior
      @   requires index < 0 || index >= this.size();
      @   assignable \nothing;
      @   signals (IndexOutOfBoundsException);
      @*/
    public Object set(int index, Object e) {}

    public boolean add(Object e) {}

    /*@ also
      @  public exceptional_behavior
      @   requires index < 0 || index >= this.size();
      @   assignable \nothing;
      @   signals (IndexOutOfBoundsException);
      @*/
    public void add(int index, Object e) {}

    /*@ also
      @  public exceptional_behavior
      @   requires index < 0 || index >= this.size();
      @   assignable \nothing;
      @   signals (IndexOutOfBoundsException);
      @*/
    public Object remove(int index) {}
    public void clear() {}
    public boolean addAll(Collection c) {}

    /*@ also
      @  public exceptional_behavior
      @   requires index < 0 || index >= this.size() || c == null;
      @   assignable \nothing;
      @   signals (IndexOutOfBoundsException) index < 0 || index >= this.size();
      @   signals (NullPointerException) c == null;
      @*/
    public boolean addAll(int index, Collection c) {}
    protected void removeRange(int fromIndex, int toIndex) {}
    private void checkBoundInclusive(int index) {}
    private void checkBoundExclusive(int index) {}
    boolean removeAllInternal(Collection c) {}
    boolean retainAllInternal(Collection c) {}
    private void writeObject(ObjectOutputStream s) throws IOException {}
    private void readObject(ObjectInputStream s)
     throws IOException, ClassNotFoundException {}
}
