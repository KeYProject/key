public class MyInteger {
   public int value;
   
   /*@ normal_behavior
     @ requires summand != null;
     @ ensures value == \old(value) + summand.value;
     @ assignable value;
     @*/
   public void compute(MyInteger summand) {
      value += summand.value;
   }
}
