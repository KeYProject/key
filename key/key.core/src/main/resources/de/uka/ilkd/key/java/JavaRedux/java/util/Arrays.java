package java.util;

public final class Arrays {

	/*@ public behavior
	  @ requires true;
	  @ ensures true;
      @ assignable \everything;
      @*/
	public static java.util.List asList(int[] arr);

	/*@ public behavior
	  @ requires true;
	  @ ensures true;
      @ assignable \everything;
      @*/
	public static java.util.List asList(char[] arr);
	
	/*@ public behavior
	  @ requires true;
	  @ ensures true;
      @ assignable \everything;
      @*/
	public static java.util.List asList(java.lang.String str);

	/*@ public behavior
	  @ requires true;
	  @ ensures true;
      @ assignable \everything;
      @*/
	public static java.util.List asList(java.lang.String[] arr);
}