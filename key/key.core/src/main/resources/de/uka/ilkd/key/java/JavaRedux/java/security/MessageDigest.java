package java.security;

public abstract class MessageDigest extends java.security.MessageDigestSpi {

   /*@ public normal_behavior
     @ assignable \nothing;
     @ determines \result \by \param0;
     @*/
   public static java.security.MessageDigest getInstance(java.lang.String param0) throws java.security.NoSuchAlgorithmException;

   /*@ public normal_behavior
     @ assignable \nothing;
     @ determines \result \by \nothing;
     @*/
   public byte[] digest(byte[] param0);

   /*@ public normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \nothing;
     @*/
   public void update(byte[] param0);

   /*@ public normal_behavior
     @ assignable \nothing;
     @ determines \result \by \nothing;
     @*/
   public byte[] digest();
}