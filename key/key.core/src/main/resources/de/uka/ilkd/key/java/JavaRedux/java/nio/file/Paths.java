package java.nio.file;

public final class Paths extends java.lang.Object {

	/*@ public behavior
	  @ requires true;
	  @ ensures true;
      @ assignable \nothing;
      @*/
	public static java.nio.file.Path get(java.lang.String param0);

   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \nothing;
     @*/
   public static java.nio.file.Path get(java.lang.String param0, java.lang.String[] param1);
}