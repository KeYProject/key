package java.lang;

public final class System {

    public static final java.io.InputStream in;
    public static final java.io.PrintStream out;
    public static final java.io.PrintStream err;

   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
	public static void arraycopy(java.lang.Object src, int srcPos, java.lang.Object dest, int destPos, int length);
	
	/*@ public behavior
	  @ ensures false;
	  @ signals_only \nothing;
      @ diverges true;
      @*/
	public static void exit(int code);
}
