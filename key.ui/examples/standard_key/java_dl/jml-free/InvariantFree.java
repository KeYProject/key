final class A { 
    int f;
    int g;
    //@ invariant f > 0;
    //@ invariant_free g > 0;
    
    /*@ normal_behavior
      @ ensures true;
      @*/
    A() {
        f = 1;
        g = 0;
    }
    
    /*@ normal_behavior
      @ ensures \result > 0;
      @*/
    int foo() {
        return g;
    }
}

final class B {
    /*@ normal_behavior
      @ ensures \result > 0;
      @*/
    int foo() {
        return new A().g;
    }
    
    /*@ normal_behavior
      @ requires \invariant_free_for(a);
      @ ensures \result > 0;
      @*/
    int bar(A a) {
        return a.g;
    }
    
    /*@ normal_behavior
      @ requires \invariant_for(a);
      @ ensures \result > 0;
      @*/
    int baz(A a) {
        return a.g;
    }
}
