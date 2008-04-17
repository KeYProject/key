import javax.realtime.*;

public class Test extends SuperTest{

    //@ public invariant oArr!=null && oArr.length>1 && next!=null;

    int attr=3;
    int[] arr;
    byte b0, b1;
    Object[] oArr;
    Test next;
    public static Object sa; 
    public static Test st;

    /*@ public normal_behavior
      @  requires oArr.memoryArea == \currentMemoryArea;
      @  assignable oArr[0];
      @  working_space \space(Test);
      @ also public normal_behavior
      @  requires oArr.memoryArea == \currentMemoryArea;
      @  assignable oArr[0];
      @  working_space 32;
      @  
      @*/
    public void createObj(){
	oArr[0] = new Test();
    }

    /*@ public normal_behavior
      @  requires oArr.memoryArea == \currentMemoryArea;
      @   {|
      @      working_space \space(Test);
      @     also
      @      working_space 32;
      @   |}
      @*/
    public void createObjectWithContract(){
	createObj();
    }

    /*@ public normal_behavior
      @  requires outerScope(\currentMemoryArea, oArr.memoryArea) &&
      @           outerScope(o.memoryArea, \currentMemoryArea); 
      @  ensures true;
      @*/
    public void createArrayWithInitializers(Object o){
	this.oArr = new Object[]{o};
    }

    /*@ public normal_behavior
      @  requires \inImmortalMemory(next) && this.next.next!=null;
      @  ensures true;
      @*/
    public void assignToStaticField1(){
	sa = next.next.next;
    }

    /*@ public normal_behavior
      @  requires \inImmortalMemory(oArr);
      @  ensures true;
      @*/
    public void assignToStaticField2(){
	sa = oArr[0];
    }

    /*@ public normal_behavior
      @  requires inOuterScope(o1, this);
      @  ensures true;
      @*/
    public void assignToInstanceField1(Test o1){
	this.next = o1;
    }

    /*@ public normal_behavior
      @  requires inOuterScope(o1, next);
      @  ensures true;
      @*/
    public void assignToInstanceField2(Test o1){
	next.next = o1;
    }

    /*@ public normal_behavior
      @  ensures true;
      @*/
    public void assignToInstanceFieldNull1(){
	this.next = null;
    }

    /*@ public normal_behavior
      @  ensures true;
      @*/
    public void assignToInstanceFieldNull2(){
	next.next = null;
    }

    /*@ public normal_behavior
      @  requires a>0 && outerScope(\currentMemoryArea, oArr.memoryArea);
      @  assignable \nothing;
      @  working_space 16+a*4;
      @ also public normal_behavior
      @  requires a<=0 && outerScope(\currentMemoryArea, oArr.memoryArea);
      @  assignable \nothing;
      @  working_space 0;
      @*/
    public Object[] createArray(int a){
	/*	TestRunnable t = new TestRunnable();
	MemoryArea.getMemoryArea(this).executeInArea(t);
	if(a>0){
	    return new int[a+1-1];
	}
	return null;*/
	if(a>0){
	    return oArr = new Object[a];
	}
    }

    /*@ public normal_behavior
      @  requires true;
      @//  working_space 2*\space(Test)+\space(TestRunnable)+
      @  //       \space(LTMemory);
      @  ensures true;
      @*/
    public void enterScope(){
	TestRunnable t = new TestRunnable(new Test(), false);
	ScopedMemory sm = new LTMemory(48);
	sm.enter(t);
    }

    /*@ public normal_behavior
      @  requires sm1!=null && sm2!=null && sm1!=sm2 &&
      @        sm1.memoryRemaining()>1000 && sm2.memoryRemaining()>1000 && 
      @        sm1.parent==null && sm2.parent==null && 
      @        outerScope(sm1.memoryArea, \currentMemoryArea) &&
      @        outerScope(sm2.memoryArea, \currentMemoryArea);
      @ //       sm1.memoryArea == \currentMemoryArea.memoryArea &&
      @ //       sm2.memoryArea == \currentMemoryArea.memoryArea;
      @ // working_space 2*\space(new Test())+\space(new TestRunnable(null, false))+
      @   //    2*\space(new EnterScopeRunnable(null, null))+\space(new ScopedMemory(100));
      @  ensures true;
      @*/
    public void testScopeCycle(ScopedMemory sm1, ScopedMemory sm2){
	TestRunnable t = new TestRunnable(new Test(), false);
	EnterScopeRunnable esr = new EnterScopeRunnable(sm2,t);
	EnterScopeRunnable esr1 = new EnterScopeRunnable(sm1, esr);
	sm2.enter(esr1);
    }

    /*@ public normal_behavior
      @  requires sm!=null && sm.memoryRemaining()>\space(Test) &&
      @           outerScope(sm, \currentMemoryArea) && sm!=\currentMemoryArea;
      @  working_space \space(new Test)+\space(new TestRunnable);
      @*/
    public void executeRunnableInArea(ScopedMemory sm){
	TestRunnable t = new TestRunnable(new Test(), true);
	sm.executeInArea(t);	
    }

    /*@ public normal_behavior
      @  requires next.next!=null && next.next.next!=null && 
      @           inOuterScope(this, oArr);
      @  ensures true;
      @*/
    public void outerScopeTransitive(){
	oArr[0] = next.next.next.next;
    }

    /*@ public normal_behavior
      @  requires oArr!=null && oArr.length>1  && inOuterScope(o, oArr);
      @  ensures true;
      @*/
    public void assignToObjectArray(Object o){
	oArr[0] = o;
    }

    /*@ public normal_behavior
      @  requires oArr!=null && oArr.length>1  && inOuterScope(o, oArr);
      @  ensures true;
      @*/
    public void assignToObjectArrayNull(Object o){
	oArr[0] = null;
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
      @  working_space i*\space(int[3]);
      @*/
    public void testLoop(int i){
	/*@ loop_invariant i>=0;
	  @ assignable i;
	  @ decreases i;
	  @ working_space_single_iteration \space(new int[3]);
	  @*/
	while(i>0){
	    i--;
	    int[] arr = new int[3];
	    if(i==10){
		break;
	    }
	    if(i==5) continue;
	}
    }

}
