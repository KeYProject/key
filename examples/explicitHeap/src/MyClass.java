class MyClass {
    int attr;
    int attr2;
    
    
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
    
}