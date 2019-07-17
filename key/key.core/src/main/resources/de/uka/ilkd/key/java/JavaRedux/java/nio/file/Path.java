package java.nio.file;

/**
 * @generated
 */
public interface Path extends java.lang.Comparable, java.lang.Iterable, java.nio.file.Watchable {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public abstract java.lang.String toString();

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public abstract java.nio.file.Path resolve(java.lang.String param0);
}