public class Middle{

    /*@ public normal_behavior
      @  ensures \result==x || \result==y || \result==z;
      @  ensures \result<=y && \result<=z || \result<=x && \result<=z ||
      @          \result<=x && \result<=y;
      @  ensures \result>=y && \result>=z || \result>=x && \result>=z ||
      @          \result>=x && \result>=y;
      @*/
    public static int middle(int x, int y, int z){
	int mid = z;
	if(y<z){
	    if(x<y){
		mid = y;
	    }else if(x<z){
		mid = x;
	    }
	}else{
	    if(x>y){
		mid = y;
	    }else if(x>z){
		mid = x;
	    }
	}
	return mid;
    }

}
