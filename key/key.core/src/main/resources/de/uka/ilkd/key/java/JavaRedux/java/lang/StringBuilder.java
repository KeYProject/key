package java.lang;

public final class StringBuilder implements java.io.Serializable, java.lang.Appendable {

   /*@ public behavior
	 @ requires true;
	 @ ensures true;
	 @ assignable \everything;
	 @*/
	public StringBuilder();

   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public StringBuilder(int param0);

   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public java.lang.StringBuilder append(char param0);
}