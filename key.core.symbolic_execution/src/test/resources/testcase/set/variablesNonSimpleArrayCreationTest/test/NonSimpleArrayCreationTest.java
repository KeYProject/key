public class NonSimpleArrayCreationTest {
   private static NonSimpleArrayCreationTest[] array;
   
   private int value;
   
   //@ requires n >= 4;
   //@ requires instance.value == 100;
   public static NonSimpleArrayCreationTest[] main(int n, NonSimpleArrayCreationTest instance) {
      array = new NonSimpleArrayCreationTest[n];
      array[0] = instance;
      array[1] = array[2];
      array[3] = array[0];
      return array;
   }
}
