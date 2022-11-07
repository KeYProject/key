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

	/*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ ensures (\forall \bigint i; fromIndex <= i && i < toIndex; a[i] == val);
      @ assignable a[fromIndex..toIndex - 1];
      @*/
	public static void fill(float[] a, int fromIndex, int toIndex, float val);

	/*@ public normal_behavior
      @ ensures (\forall \bigint i; 0 <= i && i < a.length; a[i] == val);
      @ assignable a[*];
      @*/
	public static void fill(boolean[] a, boolean val);

	/*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ ensures (\forall \bigint i; fromIndex <= i && i < toIndex; a[i] == val);
      @ assignable a[fromIndex..toIndex - 1];
      @*/
	public static void fill(boolean[] a, int fromIndex, int toIndex, boolean val);

	/*@ public normal_behavior
      @ ensures (\forall \bigint i; 0 <= i && i < a.length; a[i] == val);
      @ assignable a[*];
      @*/
	public static void fill(int[] a, int val);

	/*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ ensures (\forall \bigint i; fromIndex <= i && i < toIndex; a[i] == val);
      @ assignable a[fromIndex..toIndex - 1];
      @*/
	public static void fill(int[] a, int fromIndex, int toIndex, int val);

	/*@ public normal_behavior
      @ ensures (\forall \bigint i; 0 <= i && i < a.length; a[i] == val);
      @ assignable a[*];
      @*/
	public static void fill(long[] a, long val);

	/*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ ensures (\forall \bigint i; fromIndex <= i && i < toIndex; a[i] == val);
      @ assignable a[fromIndex..toIndex - 1];
      @*/
	public static void fill(long[] a, int fromIndex, int toIndex, long val);

	/*@ public normal_behavior
      @ ensures (\forall \bigint i; 0 <= i && i < a.length; a[i] == val);
      @ assignable a[*];
      @*/
	public static void fill(byte[] a, byte val);

	/*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ ensures (\forall \bigint i; fromIndex <= i && i < toIndex; a[i] == val);
      @ assignable a[fromIndex..toIndex - 1];
      @*/
	public static void fill(byte[] a, int fromIndex, int toIndex, byte val);

	/*@ public normal_behavior
      @ ensures (\forall \bigint i; 0 <= i && i < a.length; a[i] == val);
      @ assignable a[*];
      @*/
	public static void fill(double[] a, double val);

	/*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ ensures (\forall \bigint i; fromIndex <= i && i < toIndex; a[i] == val);
      @ assignable a[fromIndex..toIndex - 1];
      @*/
	public static void fill(double[] a, int fromIndex, int toIndex, double val);

	/*@ public normal_behavior
      @ ensures (\forall \bigint i; 0 <= i && i < a.length; a[i] == val);
      @ assignable a[*];
      @*/
	public static void fill(float[] a, float val);

	/*@ public normal_behavior
      @ requires 0 <= fromIndex <= toIndex <= a.length;
      @ ensures (\forall \bigint i; fromIndex <= i && i < toIndex; a[i] == val);
      @ assignable a[fromIndex..toIndex - 1];
      @*/
	public static void fill(float[] a, int fromIndex, int toIndex, float val);
}