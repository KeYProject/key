public class MyInteger {
   public int value;
   
   /*@ normal_behavior
     @ ensures value == \old(value) + summand.value;
     @ assignable value;
     @*/
   public void add(MyInteger summand) {
      value += summand.value;
   }
}
