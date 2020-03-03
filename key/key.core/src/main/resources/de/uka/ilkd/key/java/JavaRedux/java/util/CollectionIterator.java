package java.util;

/*
 * This final implementation of the Iterator interface is used for the iterators returned
 * by the JavaRedux library.
 * 
 * It thus models the various implementation-dependent Iterator classes used in a Java
 * library. Since these are not visible to the library user, they are -- like this class --
 * effectively final and their public invariant is equivalent to that of the Iterator interface.
 */
public final class CollectionIterator implements Iterator { }
