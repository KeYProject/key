package resolver.test.parameterizedTypeTest;

public class Main2<T> {
   
   T field;
   Object o;
   
   //@ invariant field.equals(o);
   
   //@ invariant somethingThatDoesNotExist;
   
   //@ invariant \result;
}