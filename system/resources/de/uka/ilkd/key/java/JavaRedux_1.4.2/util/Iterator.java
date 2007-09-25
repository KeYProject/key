package java.util;
public interface Iterator
{

    /*@ public model instance boolean moreElements;
      @                               in objectState;
      @*/

    //@ instance ghost public \TYPE elementType;

    //@ instance ghost public boolean returnsNull;

    //@ public instance ghost boolean remove_called_since;

    /*@ public normal_behavior
      @     requires n >= 0;
      public pure model boolean hasNext(int n);  
      @*/

    /*@ public normal_behavior
      @    requires n >= 0 && hasNext(n);
      @    ensures (* \result is the nth, counting from 0,
      @             next element that would be returned by this iterator *);
      @    ensures !returnsNull ==> \result != null;
      @    ensures \result == null || \typeof(\result) <: elementType;
      @ for_example
      @    public normal_example
      @      requires n == 0 && moreElements;
      @      ensures (* \result == the object that would be
      @                 returned by calling next() *);
      public pure model Object nthNextElement(int n);  
      @*/


    /*@ public normal_behavior
      @    assignable objectState;
      @    ensures \result <==> moreElements;
      @*/
    boolean hasNext();
    

    /*@  public normal_behavior
      @     requires moreElements;
      @     requires_redundantly hasNext(0);
      @     assignable objectState, remove_called_since, moreElements;
      @     ensures !remove_called_since;
      @     ensures (\result == null) || \typeof(\result) <: elementType;
      @     ensures !returnsNull ==> (\result != null);
      @ also
      @   public exceptional_behavior
      @     requires !moreElements;
      @     assignable \nothing;
      @     signals (NoSuchElementException);
      @*/
    Object next();


    /*@ public behavior
      @   assignable objectState, remove_called_since;
      @   ensures !\old(remove_called_since) && remove_called_since;
      @   signals (UnsupportedOperationException);
      @   signals (IllegalStateException) \old(remove_called_since);
      @*/    
    void remove();
}
