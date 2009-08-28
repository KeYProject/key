class MyClass {
    int attr;
    int attr2;
    
    //@ accessible <inv>: this.*;
    
    /*@ normal_behavior
      @   assignable attr;
      @   ensures \result == i + 27 && attr == \result;
      @*/
    int add27(int i) {
	attr = i + 27;
	return attr;
    }
    
        
    /*@ normal_behavior
      @   requires attr2 != 358;
      @   assignable attr; 
      @   ensures attr == 27;
      @   diverges true;
      @ also exceptional_behavior
      @   requires attr2 == 358;
      @   assignable \nothing;
      @   signals_only RuntimeException;
      @*/
    void loop1() {
	if(attr2 == 358) {
	    throw new RuntimeException();
	}
        /*@ loop_invariant 0 <= i && i <= 3 && (i > 0 ==> attr == 27);
          @ assignable attr;
          @*/
        for(int i = 0; i < 3; i++) {
            add27(0);
        }
    }
    
    
    /*@ normal_behavior
      @   assignable a[*]; 
      @   ensures (\forall int x; 0 <= x && x < a.length; a[x] == \old(attr2));
      @*/
    void loop2(int[] a) {
        int j = 0;
        /*@ loop_invariant 0 <= i && i <= a.length && (\forall int x; 0 <= x && x < i; a[x] == \old(attr2));
          @ assignable a[*];
          @ decreases a.length - i;
          @*/
        for(int i = 0; i < a.length; i++) {
            a[i] = j + attr2;
        }
    }

    
    /*@ normal_behavior
      @   assignable a[*];
      @   ensures (\forall int x, y; 0 < x && x < y && y < a.length; a[x] <= a[y]);
      @   diverges true;
      @*/
    static void selectionSort(int[] a) {
        /*@ loop_invariant 0 <= i && i <= a.length 
          @                && (\forall int x, y; 0 <= x && x < y && y < i; a[x] <= a[y])
          @                && (\forall int x, y; 0 <= x && x < i && i <= y && y < a.length; a[x] <= a[y]);
          @ assignable a[*];
          @ //assignable i, a[*];          
          @*/
        for(int i = 0; i < a.length; i++) {
            int minIndex = i;
            /*@ loop_invariant i < j && j <= a.length
              @                && i <= minIndex && minIndex < j
              @                && (\forall int x; i <= x && x < j; a[minIndex] <= a[x]);
              @ assignable \nothing;
              @ //assignable j, minIndex; 
              @*/
            for(int j = i + 1; j < a.length; j++) {
                if(a[j] < a[minIndex]) minIndex = j;
            }
            int temp = a[i];
            a[i] = a[minIndex];
            a[minIndex] = temp;
        }
    }
}
