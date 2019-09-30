package java.util;

public final class Arrays {

	/*@ public normal_behavior
	  @ ensures \invariant_for(\result);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
	public static java.util.ArrayList asList(int[] arr);

	/*@ public normal_behavior
      @ ensures \invariant_for(\result);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
	public static java.util.ArrayList asList(char[] arr);
	
	/*@ public normal_behavior
      @ ensures \invariant_for(\result);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
	public static java.util.ArrayList asList(java.lang.String str);

	/*@ public normal_behavior
      @ ensures \invariant_for(\result);
      @ ensures \fresh(\result);
      @ assignable \nothing;
      @*/
	public static java.util.ArrayList asList(java.lang.String[] arr);
}