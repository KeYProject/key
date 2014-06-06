
public class BreakpointStopCallerAndLoop {
   
   private BreakpointStopCallee callee;
   
   private int x;
   
   public int loop(){
      for(int i=0;i<=3;i++){
      x++;
      }
      return x;
   }
   
	public int main(int a) {
	   a++;
      x = callee.main(a);
      x = callee.main(a);
	   x++;
      loop();
      loop();
      loop();
	   return x;
	}
}
