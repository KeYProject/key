package java.security;

public abstract class KeyPairGenerator extends java.security.KeyPairGeneratorSpi {
   public static java.security.KeyPairGenerator getInstance(java.lang.String param0, java.lang.String param1) throws java.security.NoSuchAlgorithmException, java.security.NoSuchProviderException;
   public void initialize(int param0);
   public java.security.KeyPair generateKeyPair();
}