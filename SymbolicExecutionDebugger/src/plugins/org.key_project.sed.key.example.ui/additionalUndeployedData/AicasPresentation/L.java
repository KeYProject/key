package example7;

public class L {
	public /*@ nullable @*/ L next;
	public int content;
	
	/*@ public normal_behavior
	  @ requires l != null && a.length == sz && sz >= 0;
	  @ ensures true;
	  @*/
	public static void copy(L l, int[] a, int sz) {		
		L tail = l;
		for (int i = 0; tail != null && i < sz; i++) {
			a[i] = tail.content;
			tail = tail.next;
		}
	}
	
	
	/*@ public normal_behavior
	  @ requires l != null;
	  @ ensures true;
	  @*/
	public static int sum(L l) {		
		int sum = 0;
		L tail = l;
		while (tail != null) {
			sum += tail.content;
			tail = tail.next;
		}
		return sum;
	}
	
	/*@ public normal_behavior
	  @ requires n != null && hd !=null;
	  @ ensures n.next == \old(hd.next);
	  @ assignable hd.next, n.next;
	  @*/
	public static void insert(L hd, L n) {
		n.next = hd.next;
	}
	
}