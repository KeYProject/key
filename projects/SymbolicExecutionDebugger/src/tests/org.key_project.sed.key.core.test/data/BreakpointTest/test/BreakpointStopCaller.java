
public class BreakpointStopCaller {
   
   private BreakpointStopCallee callee;
   
   private int x;
   
   public int loop(){
      for(int i = 0;i <= 3;i++){
         x++;
      }
      return x;
   }
   public int main() {
     x++;
     x++;
     loop();
     return x;
   }
}
