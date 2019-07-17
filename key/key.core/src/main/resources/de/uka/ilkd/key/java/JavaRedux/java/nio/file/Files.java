package java.nio.file;

public final class Files extends java.lang.Object {
	


	/*@ public behavior
	  @ requires true;
	  @ ensures true;
	  @ assignable \everything;
	  @*/
	public static java.nio.file.Path write(java.nio.file.Path param0, byte[] param1) throws java.io.IOException;

   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public static java.nio.file.Path write(java.nio.file.Path param0, byte[] param1, java.nio.file.OpenOption[] param2) throws java.io.IOException;
}