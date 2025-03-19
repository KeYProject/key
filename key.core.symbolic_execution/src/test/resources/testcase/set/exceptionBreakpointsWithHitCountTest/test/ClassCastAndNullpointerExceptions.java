
public class ClassCastAndNullpointerExceptions {
	
	private  ClassCastAndNullpointerExceptions next;
	
	private int x;
	
	ClassCastAndNullpointerExceptions castable;
	
	public int main() {
		ClassCastInherit castInto = (ClassCastInherit)castable;
		if(x>0){
			try{
				return next.x;
				}
			catch(NullPointerException e){
					return x;
				}
		}
      next.next.x=0;
      next.next.next.x=0;
      return next.next.next.next.x;
	}
}
