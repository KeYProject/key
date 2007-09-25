public class list {
    public list next, prev;

    public static list rev(list a) {
	list res = null;
	while (a != null) {
	    res = a;
	    final list t = a.next;
	    a.next = a.prev;
	    a.prev = t;
	    a = t;
	}
	return res;
    }
}
