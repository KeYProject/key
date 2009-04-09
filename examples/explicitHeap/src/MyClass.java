class MyClass {
    int attr;
    int attr2;
    MyClass next;
    
    
    /*@ normal_behavior
      @   ensures attr > \old(attr);
      @*/
    void m() {
        attr++;
    }
    
    
    /*@ normal_behavior
      @   requires attr2 == 358;
      @   assignable attr; 
      @   ensures attr == 27 && attr2 == 358;
      @   diverges true;
      @*/
    void verySimpleLoop() {
        /*@ loop_invariant 0 <= i && i <= 3 && (i > 0 ==> attr == 27);
          @ assignable i, attr;
          @*/
        for(int i = 0; i < 3; i++) {
            attr = 27;
        }
    }
    
    
    
    /*@ normal_behavior
      @   assignable a[*]; 
      @   ensures (\forall int x; 0 <= x && x < a.length; a[x] == 0);
      @   diverges true;
      @*/
    void slightlyMoreInterestingLoop(int[] a) {
        int j = 0;
        /*@ loop_invariant 0 <= i && i <= a.length && (\forall int x; 0 <= x && x < i; a[x] == 0);
          @ assignable i, a[*];
          @*/
        for(int i = 0; i < a.length; i++) {
            a[i] = j;
        }
    }
    
    
    /*@ normal_behavior
      @   assignable a[*];
      @   ensures (\forall int x, y; 0 < x && x < y && y < a.length; a[x] <= a[y]);
      @   diverges true;
      @*/
    void selectionSort(int[] a) {
        /*@ loop_invariant 0 <= i && i <= a.length 
          @                && (\forall int x, y; 0 <= x && x < y && y < i; a[x] <= a[y])
          @                && (\forall int x, y; 0 <= x && x < i && i <= y && y < a.length; a[x] <= a[y]);
          @ assignable i, a[*];
          @*/
        for(int i = 0; i < a.length; i++) {
            int minIndex = i;
            /*@ loop_invariant i < j && j <= a.length
              @                && i <= minIndex && minIndex < j
              @                && (\forall int x; i <= x && x < j; a[minIndex] <= a[x]);
              @ assignable j, minIndex; 
              @*/
            for(int j = i + 1; j < a.length; j++) {
                if(a[j] < a[minIndex]) minIndex = j;
            }
            int temp = a[i];
            a[i] = a[minIndex];
            a[minIndex] = temp;
        }
    }
    
    
    /*@ normal_behavior
      @   requires n >= 0;
      @   ensures \result.length == n;
      @   ensures (\forall int x; 0 <= x && x < n; \result[x] == 0);
      @*/
    int[] createArray(int n) {
	int[] a = new int[n];
	return a;
    }
}