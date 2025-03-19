public class EnoughInfoReturn {
	private int[] passwords;
	private boolean found;

	public void passwordChecker(){
		int i = 0;
		
		/*@ loop_invariant i >= 0 & (\forall int j_5; j_5 < i && 0 <= j_5; passwords[j_5] >= 0);
        @ assignable i;
        @ decreases passwords.length - i;
        @*/
		while (i < passwords.length && passwords[i] >= 0) {
			i += 1;
		}
		found = i < passwords.length;
	}
}