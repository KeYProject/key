
public class ClassCastAndNullpointerExceptions {
	
	private  ClassCastAndNullpointerExceptions next;
	
	private int x;
	
	ClassCastAndNullpointerExceptions castable;
	
	public int main() {
		ClassCastInherit castInto = (ClassCastInherit)castable;
		if(x>0){
			try{
			   castInto = (ClassCastInherit)castable;
				return next.x;
				}
			catch(Exception e){
					return x;
				}
		}
      next.next.x=0;
      next.next.next.x=0;
      return next.next.next.next.x;
	}
}
