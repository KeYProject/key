import javax.realtime.*;

public class Test extends SuperTest{

    int attr;
    int[] arr;
    byte b0, b1;
    Object[] oArr;

    /*@ public normal_behavior
      @  working_space \space(new Test());
      @ also public normal_behavior
      @  working_space 24;
      @*/
    public void createObj(){
	new Test();
    }

    /*@ public normal_behavior
      @  requires a>0;
      @  assignable \nothing;
      @  working_space 16+a*4;
      @ also public normal_behavior
      @  requires a<=0;
      @  assignable \nothing;
      @  working_space 0;
      @*/
    public int[] createArray(int a){
	TestRunnable t = new TestRunnable();
	MemoryArea.getMemoryArea(this).executeInArea(t);
	if(a>0){
	    return new int[a+1-1];
	}
	return null;
    }

    /*@ public normal_behavior
      @  requires oArr!=null && oArr.length>1 && oArr.memoryArea==o.memoryArea && inOuterScope(o, oArr);
      @  ensures true;
      @*/
    public void assignToObjectArray(Object o){
	oArr[0] = o;
    }

    /*@ public normal_behavior
      @  assignable arr;
      @  working_space \working_space_rigid(createArray(int arg), arg==7);
      @ also public normal_behavior
      @  assignable arr;
      @  working_space \working_space(createArray(7));
      @*/
    public void initArr(int a){
	arr = createArray(7);
    }

    /*@ public normal_behavior
      @  assignable \nothing;
      @  working_space 50;
      @*/
    public void testContract2(){
	initArr(0);
    }

    /*@ public normal_behavior
      @  requires i>0;
      @  assignable \nothing;
      @  working_space i*\space(new int[3]);
      @*/
    public void testLoop(int i){
	/*@ loop_invariant i>=0;
	  @ assignable i;
	  @ decreases i;
	  @ working_space_single_iteration \space(new int[3]);
	  @*/
	while(i>0){
	    int[] arr = new int[3];
	    if(i==10) break;
	    if(i==5) continue;
	    i--;
	}
    }

}
