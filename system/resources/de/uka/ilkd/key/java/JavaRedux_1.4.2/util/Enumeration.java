package java.util;

public interface Enumeration
{

    /*@ public model instance boolean moreElements;
      @                               in objectState;
      @*/

    //@ instance ghost public \TYPE elementType;

    //@ instance ghost public boolean returnsNull;

    /*@ public normal_behavior
      @    assignable objectState;
      @    ensures \result <==> moreElements;
      @*/
  boolean hasMoreElements();


    /*@   public normal_behavior
      @     requires moreElements;
      @     assignable objectState;
      @     assignable moreElements;
      @     ensures (\result == null) || \typeof(\result) <: elementType;
      @     ensures !returnsNull ==> (\result != null);
      @ also
      @   public exceptional_behavior
      @     requires !moreElements;
      @     assignable \nothing;
      @     signals (NoSuchElementException);
      @*/
  Object nextElement();
}
