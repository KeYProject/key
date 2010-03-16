import javax.realtime.*;

public class UseFastMap{

    /*@ public normal_behavior
      @  requires \outerScope(\memoryArea(a), \memoryArea(fm)) && 
      @     \outerScope(\memoryArea(b), \memoryArea(fm));
      @  requires \memoryArea(fm).memoryRemaining() >=
      @      (\currentMemoryArea==\memoryArea(fm) ? \space(LTMemory)+\space(Runnable) : 0) + 4*\space(Entry);
      @  working_space (\currentMemoryArea==\memoryArea(fm) ? 4*\space(Entry) : 0)+\space(LTMemory)+\space(Runnable); 
      @*/
    public static void addToFastMapInScope(MyObject a, MyObject b, FastMap fm){
	ScopedMemory m = new LTMemory(2000);
	Runnable r = new Runnable(){
		public void run(){
		    fm.put(a,b);
		}
	    };
	m.enter(r);
    }

}
