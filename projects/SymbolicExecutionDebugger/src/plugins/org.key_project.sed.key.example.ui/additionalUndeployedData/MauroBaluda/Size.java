

public class Size {
	public static int getStatus(int[] valvesStatus, int i, int size) throws Exception {
		if (i < 0 | i >= size) {
			throw new Exception();
		}
		else {
			return valvesStatus[i];
		}
	}
	
	public static int checkValves(int[] valvesStatus, int size) throws Exception{
		int count = 0;
		int i = 0;
		while (i < size) {
			int status = getStatus(valvesStatus, i, size);
			if (status == -1) {
				count++;
			}
			i++;
		}
		if (count > 2) {
			throw new Exception(); // Breakpoint can be used to find an execution path resulting in the invalid state
		}
		return count;
	}
	
	// The additional while loop makes it more complicated to find a path invalidating checkValves
	public static void main() throws Exception {
		int[] valvesStatus;  // reader user input
		int size; // read user input;
		int input2; //read user input2
		while (input2 > 0) {
			input2--;
		}
		checkValves(valvesStatus, size);
	}
}

// Crest (Symbolic Execution Engine for C)
