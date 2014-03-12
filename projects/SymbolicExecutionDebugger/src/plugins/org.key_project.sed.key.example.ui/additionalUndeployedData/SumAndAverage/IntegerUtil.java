
public class IntegerUtil {
	public static void main(String[] args) {
		try {
			System.out.println(sum(new int[] {1, 2, 3}));
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	public static int average(int[] a) throws Exception {
		int sum = sum(a);
		return sum / a.length;
	}

	/*@ normal_behavior
	  @ requires a != null;
	  @ ensures \result == (\sum int i; 0 <= i && i < a.length; a[i]);
	  @ assignable \nothing;
	  @
	  @ also
	  @
	  @ exceptional_behavior
	  @ requires a == null;
	  @ signals (Exception e) true;
	  @ assignable \nothing;
	  @*/
	public static int sum(/*@ nullable @*/ int[] a) throws Exception {
		if (a == null)
			throw new Exception("Array is null.");
		else {
			int sum = 0;
			/*@ loop_invariant i >= 0 && i <= a.length;
			  @ loop_invariant sum == (\sum int j; 0 <= j && j < i; a[j]);
			  @ decreasing a.length - i;
			  @ assignable sum, i;
			  @*/
			for (int i = 0; i < a.length; i++)
				sum += a[i];
			return sum;
		} }	
}
