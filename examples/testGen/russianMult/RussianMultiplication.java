public class RussianMultiplication{

    /*@ public normal_behavior
      @  requires a<Integer.MAX_VALUE && (a!=0 ==> b<=Integer.MAX_VALUE/a);
      @  requires a>Integer.MIN_VALUE && (a!=0 ==> b>=Integer.MIN_VALUE/a);
      @  ensures \result == a*b;
      @*/
    public int russianMultiplication(int a, int b){
        int z = 0;
	//This is not valid JML
	/*@ //maintaining \old(a)*\old(b)==z+a*b;
	  @ //post \old(a)*\old(b) == z;
	  @ //assignable a,b;
	  @*/
        while(a != 0){
            if(a%2 != 0){
                z = z+b;
            }
            a = a/2;
            b = b*2;
        }
        return z;
    }
    
}
