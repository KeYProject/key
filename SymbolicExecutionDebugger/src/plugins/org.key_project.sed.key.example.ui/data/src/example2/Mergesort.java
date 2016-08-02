package example2;

/**
 * This example explains how to find the origin of a bug with the help of the 
 * Symbolic Execution Debugger (SED). 
 * <p>
 * The debugging session starts directly with the method of interest:
 * <ol>
 *    <li>
 *       Debug method {@link #sort(int[])} via context menu item 
 *       'Debug As, Symbolic Execution Debugger (SED)'
 *    </li>
 *    <li>Select the start node</li>
 *    <li>
 *       In view 'Debug', perform 'Step Into' until a node representing an 
 *       uncaught {@link NullPointerException} appears (3 times)
 *    </li>
 * </ol>
 * The encountered {@link NullPointerException} is spurious as method parameter 
 * {@code intArr} should not be {@code null}. This kind of knowledge can be 
 * added by providing a precondition:
 * <ol> 
 *    <li>Terminate the debug session</li>
 *    <li>
 *       Open the debug configuration via main menu item 
 *       'Run, Debug Configurations'
 *    </li>
 *    <li>Add {@code intArr != null} as precondition</li>
 *    <li>Debug method {@link #sort(int[])} as before</li>
 *    <li>Set breakpoint at line 66: {@code if (l <= r)}</li>
 *    <li>Select the start node</li>
 *    <li>
 *       In view 'Debug', click on 'Resume'; execution will be suspended when
 *       the if-statement is reached the first time
 *    </li>
 *    <li>
 *       In view 'Debug', perform 'Step Into' and observe that execution splits
 *       in case that the array is not empty and in case it is empty
 *    </li>
 *    <li>
 *       In view 'Debug', click on 'Resume'; execution will be suspended when
 *       the if-statement is reached the second time
 *    </li>
 *    <li>
 *       In view 'Debug', perform 'Step Into' and observe that execution does
 *       not split, thus, the then branch is always taken
 *    </li>
 * </ol>
 * Two observations: First, because of the precondition no spurious exceptions 
 * are shown any longer. Second, because of the if-statement one would expect 
 * two branches. The fact that there is only one indicates a problem with the 
 * if-guard (which evaluates always to true). The guard needs to be 
 * corrected to {@code l < r}.
 * <p>
 * Modified version of the Mergesort implementation by Jörg Czeschla, see 
 * <a href="http://javabeginners.de/Algorithmen/Sortieralgorithmen/Mergesort.php">
 *    http://javabeginners.de/Algorithmen/Sortieralgorithmen/Mergesort.php
 * </a>.
 */
public class Mergesort {
   public static void sort(int[] intArr) {
      sortRange(intArr, 0, intArr.length - 1);
   }

   public static void sortRange(int[] intArr, int l, int r) {
      if (l <= r) {
         int q = (l + r) / 2;
         sortRange(intArr, l, q);
         sortRange(intArr, q + 1, r);
         merge(intArr, l, q, r);
      }
   }

   private static void merge(int[] intArr, int l, int q, int r) {
      int[] arr = new int[intArr.length];
      int i, j;
      for (i = l; i <= q; i++) {
         arr[i] = intArr[i];
      }
      for (j = q + 1; j <= r; j++) {
         arr[r + q + 1 - j] = intArr[j];
      }
      i = l;
      j = r;
      for (int k = l; k <= r; k++) {
         if (arr[i] <= arr[j]) {
            intArr[k] = arr[i];
            i++;
         }
         else {
            intArr[k] = arr[j];
            j--;
         }
      }
   }
}