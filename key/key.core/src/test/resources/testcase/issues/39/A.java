package testcase.issues;

class A {
   //@ ghost \locset l;

    //@ensures \singleton(3) == \singleton(3);
   void m() {
     //@ set l = \singleton(3);
     {}
   }
}

