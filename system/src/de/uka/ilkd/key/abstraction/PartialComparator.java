package de.uka.ilkd.key.abstraction;

/**
 * TODO: Document.
 *
 * @param <T> the type of objects that may be compared by this comparator
 * 
 * @author Dominic Scheurer
 * @see java.util.Comparator
 */
public interface PartialComparator<T> {

   /**
    * TODO: Document.
    */
   public static enum PartialComparisonResult {
      LTE, GTE, EQ, UNDEF
   }
   
   /**
    * TODO: Document.
    * 
    * @param o1
    * @param o2
    * @return
    */
   public PartialComparisonResult compare(T o1, T o2);
   
}
