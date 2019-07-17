package java.security;

/**
 * @generated
 */
public abstract class MessageDigest extends java.security.MessageDigestSpi {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public static java.security.MessageDigest getInstance(java.lang.String param0) throws java.security.NoSuchAlgorithmException;

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public byte[] digest(byte[] param0);

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void update(byte[] param0);

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public byte[] digest();
}