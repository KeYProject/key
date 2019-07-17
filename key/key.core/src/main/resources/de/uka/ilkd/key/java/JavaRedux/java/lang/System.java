package java.lang;

/**
 * @generated
 */
public final class System {

   /**
    * @generated
    */
   /*@ public behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
	public static void arraycopy(java.lang.Object src, int srcPos, java.lang.Object dest, int destPos, int length);
	
	/*@ public behavior
      @ diverges true;
      @*/
	public static void exit(int code);
}
