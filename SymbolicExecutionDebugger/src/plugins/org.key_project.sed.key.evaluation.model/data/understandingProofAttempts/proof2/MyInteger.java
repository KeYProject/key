public class MyInteger {
   public int value;
   
   /*@ normal_behavior
     @ requires summand != null;
     @ ensures value == \old(value) + summand.value;
     @*/
   public void add(MyInteger summand) {
      value += summand.value;
   }
}
