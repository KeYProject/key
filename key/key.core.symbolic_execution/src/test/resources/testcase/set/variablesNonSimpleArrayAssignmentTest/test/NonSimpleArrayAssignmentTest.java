public class NonSimpleArrayAssignmentTest {
   private int value;
   
   //@ requires array.length >= 4;
   public static NonSimpleArrayAssignmentTest[] main(NonSimpleArrayAssignmentTest[] array) {
      array[0].value = 100;
      array[1].value = array[2].value;
      array[3].value = array[0].value;
      return array;
   }
}
