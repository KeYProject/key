public class Test{

    int[] arr;

    /*@ public normal_behavior
      @  ensures true;
      @  working_space_constructed \space(int[1]);
      @*/
    public @NoLocalScope Test(){
	arr = new@<constructedScope> int[1];
    }

    /*@ public normal_behavior
      @  ensures true;
      @  working_space_caller \space(int[1]);
      @*/
    public @NoLocalScope @ExternallyConstructedScope Test(boolean a){
	arr = new@<constructedScope> int[1];
    }

    /*@ public normal_behavior
      @  working_space_local \space(Test) + \space(int[1]) + \space(LTMemory);
      @  working_space_caller \max_space(Object);
      @  ensures true;
      @  assignable \object_creation(Test), \object_creation(Object);
      @*/
    public @ExternallyConstructedScope @CallerAllocatedResult Object m1(){
	Object o = new@<localScope> Test();
	return m2()@<callerScope>;
    }

    /*@ public normal_behavior
      @  ensures true;
      @  assignable \object_creation(Test);
      @  working_space_caller \space(Test);
      @*/
    public @ExternallyConstructedScope @NoLocalScope @CallerAllocatedResult Test m2(){
	return new@<callerScope> Test();
    }

    /*@ public normal_behavior
      @  ensures true;
      @  assignable \object_creation(Test);
      @  working_space_caller \space(Test)+\space(int[1]);
      @*/
    public @NoLocalScope @CallerAllocatedResult Test m3(){
	return new@<callerScope> Test(true);
    }

    /*@ public normal_behavior
      @  requires l>0 && l<100000;
      @  assignable \object_creation(Test), \object_creation(Test[]);
      @  working_space_constructed l*\space(Test);
      @  working_space_caller \space(Test[l]);
      @*/
    public @NoLocalScope @CallerAllocatedResult Test[] loop(int l){
	Test[] result = new@<callerScope> Test[l];
	int i=0;
	/*@ loop_invariant i>=0 && i<=l;
	  @ assignable result[*],i,\object_creation(Test[]);
	  @ working_space_single_iteration_local 0;
	  @ working_space_single_iteration_reentrant 0;
	  @ working_space_single_iteration_constructed \space(Test);
	  @ decreasing l-i;
	  @*/
	while(i<l){
	    result[i++] = new@<constructedScope> Test();
	}
	return result;
    }

    /*@ public normal_behavior
      @  working_space_reentrant \space(Test) + \space(int[1]) + \space(LTMemory);
      @  ensures true;
      @*/
    public void createInReentrantScope(){
	Test t = new@<reentrantScope> Test();
    }

}
