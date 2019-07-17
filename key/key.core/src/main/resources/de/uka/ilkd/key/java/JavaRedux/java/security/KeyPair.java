package java.security;

/**
 * @generated
 */
public final class KeyPair extends java.lang.Object implements java.io.Serializable {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public KeyPair(java.security.PublicKey param0, java.security.PrivateKey param1);

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public java.security.PublicKey getPublic();

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public java.security.PrivateKey getPrivate();
}