package java.security;

/**
 * @generated
 */
public abstract class KeyPairGenerator extends java.security.KeyPairGeneratorSpi {
   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public static java.security.KeyPairGenerator getInstance(java.lang.String param0, java.lang.String param1) throws java.security.NoSuchAlgorithmException, java.security.NoSuchProviderException;

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public void initialize(int param0);

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public java.security.KeyPair generateKeyPair();
}