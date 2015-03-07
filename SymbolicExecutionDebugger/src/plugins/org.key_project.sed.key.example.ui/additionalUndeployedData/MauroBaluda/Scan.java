public class Scan {

	public static void scan(int[] array, int size, int start) throws Exception {
		while(start >= 0 && start < size){
			if (do_something(array, size, start)) {
				throw new Exception();
			}
			start = start + 1;
		}
	}

	public static boolean do_something(int[] array, int size, int item){
		if(item < 0 || item >= size){
			return true; // Unpossible to reache because of the while loop in scan
		}
		else {
			return false;
		}
		//System.out.println("Item: "+array[item]);
	}
	
//	public static void main(){
//		int size=0; 
//		int start=0;
//		int[] array = new int[size];
//		scan(array, size, start);
//	}
}