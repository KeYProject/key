package example7;

public class ListClient {

	public static L createList(int len) {
		L res = null;
		L fst = null;
		for (int i = 0; i<len; i++) {
			L l = new L(); l.content = i;
			if (i == 0) {
				fst = l;
			}
			l.next = res;
			res = l;
		}
		if (len % 9 == 0) {
			fst.next = res;
		}
		return res;
	}
	
	public static void main(String[] args) {
		int[] res;
		res = new int[40];
		L.copy(createList(3), res, res.length);
		printArray(res);

		res = new int[40];
		L.copy(createList(18), res, res.length);
		printArray(res);

		res = new int[40];
		L.copy(createList(25), res, res.length);
		printArray(res);		
	}

	private static void printArray(int[] res) {
		for (int i = 0; i<res.length; i++) {
//			  System.out.print(res[i] + "; ");
		}
//		  System.out.println();
	}
	
	
	
}


