public class MyInteger {
   public int value;
   
   /*@ normal_behavior
     @ ensures value == \old(value) + summand.value;
     @ assignable value;
     @*/
   public void add(/*@ non_null @*/ MyInteger summand) {
      value += summand.value;
   }
}
