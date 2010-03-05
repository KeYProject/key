import javax.realtime.*;

public class Test extends SuperTest{

    //@ public invariant oArr!=null && oArr.length>1 && next!=null;
    //@ private invariant \typeof(oArr) == \type(Object[]);

    int attr=3;
    int[] arr;
    byte b0, b1;
    Object[] oArr;
    Test next;
    public static Object sa; 
    public static Test st;


    /*@ public normal_behavior
      @  requires \memoryArea(oArr) == \currentMemoryArea;
      @  assignable oArr[0], \object_creation(Test);
      @  working_space \space(Test);
      @ also public normal_behavior
      @  requires \memoryArea(oArr) == \currentMemoryArea;
      @  assignable oArr[0], \object_creation(Test);
      @  working_space 40;
      @  
      @*/
    public void createObj(){
	oArr[0] = new Test();
    }

    /*@ public normal_behavior
      @  requires \memoryArea(oArr) == \currentMemoryArea;
      @   {|
      @      working_space \space(Test);
      @     also
      @      working_space 40;
      @   |}
      @*/
    public void createObjectWithContract(){
	createObj();
    }

    /*@ public normal_behavior
      @  requires \outerScope(\currentMemoryArea, \memoryArea(oArr)) &&
      @           \outerScope(\memoryArea(o), \currentMemoryArea); 
      @  assignable oArr, \object_creation(Object);
      @  working_space \space(Object[1]);
      @  ensures true;
      @*/
    public void createArrayWithInitializers(Object o){
	this.oArr = new Object[]{o};
    }

    /*@ public normal_behavior
      @  requires \currentMemoryArea==sm1;
      @  working_space \space(Runnable);
      @*/
    public void enterCurrentMem(final ScopedMemory sm1){
	final Runnable hello = new Runnable(){
		public void run(){
		    int i=0;
		    i++;
		}
	    };
	sm1.enter(hello);
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
      @  requires \inOuterScope(o1, this);
      @  ensures true;
      @*/
    public void assignToInstanceField1(Test o1){
	this.next = o1;
    }

    /*@ public normal_behavior
      @  requires \inOuterScope(o1, next);
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
      @  requires \outerScope(\memoryArea(this), \currentMemoryArea);
      @  working_space 10000;
      @  ensures true;
      @*/
    private void testOrder(){
	final LTMemory ltm1 = new LTMemory(3000000);
	final Runnable r = new Runnable(){
		public void run(){
		    final LTMemory ltm3 = new LTMemory(3000000);
		    enterArea(ltm1, ltm3);
		    /*		    ltm1.executeInArea( new Runnable(){
			    public void run(){
				ltm3.enter(hello);
			    }
			    });*/
		}
	    };
	ltm1.enter(new Runnable(){
		public void run(){
		    final LTMemory ltm2 = new LTMemory(3000000);
		    ltm2.enter(r);
		}
	    });
    }

    /*@ public normal_behavior
      @  ensures \outerScope(\memoryArea(\memoryArea(this)), \memoryArea(this));
      @*/
    public void testMemoryAreaOuter(){}

    /*@ public normal_behavior
      @  requires sm2.parent==sm1 || sm2.parent==null;
      @  requires \outerScope(sm1, \currentMemoryArea);
      @  working_space 2*\space(Runnable);
      @*/
    public void enterArea(final ScopedMemory sm1, final ScopedMemory sm2){
	final Runnable hello = new Runnable(){
		public void run(){
		    int i=0;
		    i++;
		}
	    };
	sm1.executeInArea( new Runnable(){
			    public void run(){
				sm2.enter(hello);
			    }
			});
    }

    /*@ public normal_behavior
      @  requires \outerScope(\memoryArea(this), \currentMemoryArea);
      @  working_space 10000;
      @  ensures true;
      @*/
    private void testOrderWithAssignment(){
	final LTMemory ltm1 = new LTMemory(3000000);
	final Runnable r = new Runnable(){
		public void run(){
		    final LTMemory ltm3 = new LTMemory(3000000);
		    RefCont rc = new RefCont();
		    enterAreaWithAssignment(ltm1, ltm3, rc);
		}
	    };
	ltm1.enter(new Runnable(){
		public void run(){
		    final LTMemory ltm2 = new LTMemory(3000000);
		    ltm2.enter(r);
		}
	    });
    }

    public void enterAreaWithAssignment(final ScopedMemory sm1, final ScopedMemory sm2, final RefCont rc){
	sm1.executeInArea( new Runnable(){
		Runnable r = new AssignmentRunnable(rc);
			    public void run(){
				sm2.enter(r);
			    }
			});
    }

    /*@ public normal_behavior
      @  ensures true;
      @*/
    public void assignToInstanceFieldNull2(){
	next.next = null;
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
    public Object[] createArray(int a){
	/*	TestRunnable t = new TestRunnable();
	MemoryArea.getMemoryArea(this).executeInArea(t);
	if(a>0){
	    return new int[a+1-1];
	}
	return null;*/
	if(a>0){
	    return new Object[a];
	}
	return null;
    }

    /*@ public normal_behavior
      @  requires \outerScope(\memoryArea(this), \currentMemoryArea);
      @  working_space \space(Test)+\space(Runnable)+
      @         \space(LTMemory)+24;
      @  ensures true;
      @*/
    public void enterScope(){
	final Test t = new Test();
	ScopedMemory sm = new LTMemory(48);
	sm.enter(new Runnable(){
		public void run(){
		    Test nt = new Test();
		    nt.next = t;
		}
	    });
    }

    /*@ public normal_behavior
      @  requires sm1!=null && sm2!=null && sm1!=sm2 &&
      @        sm1.memoryRemaining()>1000 && sm2.memoryRemaining()>1000 && 
      @        sm1.parent==null && sm2.parent==null && 
      @        \outerScope(\memoryArea(this), \currentMemoryArea) &&
      @        \outerScope(\memoryArea(sm1), \currentMemoryArea) &&
      @        \outerScope(\memoryArea(sm2), \currentMemoryArea);
      @ //       sm1.memoryArea == \currentMemoryArea.memoryArea &&
      @ //       sm2.memoryArea == \currentMemoryArea.memoryArea;
      @  working_space 2*\space(Test)+\space(TestRunnable)+
      @     2*\space(EnterScopeRunnable)+\space(ScopedMemory);
      @  ensures true;
      @*/
    public void testScopeCycle(ScopedMemory sm1, ScopedMemory sm2){
	final Test t = new Test();
	EnterScopeRunnable esr = new EnterScopeRunnable(sm2,new Runnable(){
		public void run(){
		    Test nt = new Test();
		    nt.next = t;
		}
	    });
	EnterScopeRunnable esr1 = new EnterScopeRunnable(sm1, esr);
	//	sm2.enter(esr1);
	sm1.enter(esr);
    }

    /*@ public normal_behavior
      @  requires sm!=null && sm.memoryRemaining()>\space(Test) &&
      @           \outerScope(sm, \currentMemoryArea) && sm!=\currentMemoryArea;
      @  working_space \space(Test)+\space(TestRunnable);
      @*/
    public void executeRunnableInArea(ScopedMemory sm){
	TestRunnable t = new TestRunnable(new Test(), true);
	sm.executeInArea(t);	
    }

    /*@ public normal_behavior
      @  requires next.next!=null && next.next.next!=null && 
      @           \inOuterScope(next, oArr);
      @  ensures true;
      @*/
    public void outerScopeTransitive(){
	oArr[0] = next.next.next.next;
    }

    /*@ public normal_behavior
      @  requires oArr!=null && oArr.length>1  && \inOuterScope(o, oArr);
      @  ensures true;
      @*/
    public void assignToObjectArray(Object o){
	oArr[0] = o;
    }

    /*@ public normal_behavior
      @  requires oArr!=null && oArr.length>1  && \inOuterScope(o, oArr);
      @  ensures true;
      @*/
    public void assignToObjectArrayNull(Object o){
	oArr[0] = null;
    }

    /*@ public normal_behavior
      @  requires \outerScope(\currentMemoryArea, \memoryArea(oArr));
      @  assignable arr;
      @  working_space \rigid_working_space(createArray(int arg), self, 
      @        arg==7 &&
      @    \outerScope(\currentMemoryArea, \memoryArea(self.oArr)));
      @ also public normal_behavior
      @  requires \outerScope(\currentMemoryArea, \memoryArea(oArr));
      @  assignable arr;
      @  working_space \working_space(createArray(7));
      @*/
    public void initArr(int a){
	arr = createArray(7);
    }

    /*@ public normal_behavior
      @  requires \outerScope(\currentMemoryArea,\memoryArea(this)) && \outerScope(\currentMemoryArea, \memoryArea(oArr));
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
	  @ assignable i, \object_creation(int[]);
	  @ decreases i;
	  @ working_space_single_iteration \space(int[3]);
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

    /*@ public normal_behavior
      @  requires a.length>0 && \outerScope(\memoryArea(a[0]),\memoryArea(this));
      @*/
    public void testAssignmentArray4(Test[] a){
	next=a[0];
    }

}
