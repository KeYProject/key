package java.security;


public final class SecureRandom extends java.util.Random {
    
   /*@ public normal_behavior
     @ assignable param0[*];
     @ determines param0[*] \by \nothing;
     @*/
   public void nextBytes(byte[] param0);

   /*@ public normal_behavior
     @ assignable \nothing;
     @*/
   public SecureRandom();

   /*@ public normal_behavior
     @ assignable \nothing;
     @ determines \result \by \nothing;
     @*/
   public static java.security.SecureRandom getInstanceStrong() throws java.security.NoSuchAlgorithmException;
}