package example2;

import java.util.Arrays;
import java.util.Random;

/**
 * An example application using the sorting algorithm implemented in class 
 * {@link Mergesort}. For more details, read the documentation of 
 * {@link Mergesort}. Have fun finding the bug!
 */
public class MergesortExample {
   public static void main(String[] args) { 
      // Create array with random numbers
      int[] intArr = new int[5];
      Random random = new Random();
      for (int i = 0; i < intArr.length; i++) {
         intArr[i] = random.nextInt(intArr.length);
      }
      // Sort array
      Mergesort.sort(intArr); 
      // Print sorted array
      System.out.println(Arrays.toString(intArr));
   }
}
