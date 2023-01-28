public class Loop {
	private int content;
	
	public void magic(Loop l) {
		int x = 3;
		while(x > 0) {
			x--;
			if(content == l.content && x < 1)
				return;
		}
			
		int j = 3;
	}
}