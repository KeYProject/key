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
      @ ensures \fresh(\result) && \fresh(\result.*);
      @ ensures \invariant_for(\result);
      @ ensures (\forall \bigint i; 0 <= i && i < \result.seq.length; ((String)\result.seq[i]) != null);
      @ assignable \nothing;
      @*/
	public static java.util.ArrayList asList(java.lang.String str);

	/*@ public normal_behavior
      @ ensures \fresh(\result) && \fresh(\result.*);
      @ ensures \invariant_for(\result);
      @ ensures (\forall \bigint i; 0 <= i && i < \result.seq.length; ((String)\result.seq[i]) != null);
      @ assignable \nothing;
      @*/
	public static java.util.ArrayList asList(java.lang.String[] arr);
}