package resolver.test.parameterizedTypeTest;

public class Main<T extends Bound1 & IBound2 & IBound3> {
   public void methodInMain() {};
   
   T field;
   
   
   //@ invariant field.methodFromBound1();
   
   //@ invariant field.methodFromIBound2();
   
   //@ invariant field.methodFromIBound3();
   
   //@ invariant field.methodFromIBound3().field;
   
   //@ invariant ((T)field).methodFromIBound3();
   
   
}