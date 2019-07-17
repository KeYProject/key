package java.security;

/**
 * @generated
 */
public class SecureRandom extends java.util.Random {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void nextBytes(byte[] param0);

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public SecureRandom();

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public static java.security.SecureRandom getInstanceStrong() throws java.security.NoSuchAlgorithmException;
}