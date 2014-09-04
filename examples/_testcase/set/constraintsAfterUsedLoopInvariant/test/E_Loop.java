public class E_Loop {
   private int high;
   public int low;
    /*@ requires high>0;
    @*/
   public void calculate(){
      low = 0;
      int i = 0;
      /*@ loop_invariant i<= high+1 && (low*2 == i*(i-1));            
      @decreases high-i+1;
      @assignable low;
      @*/ 
      while(i<=high){                 
         low = low + i;
         i = i+1;
      } 
   }
}
