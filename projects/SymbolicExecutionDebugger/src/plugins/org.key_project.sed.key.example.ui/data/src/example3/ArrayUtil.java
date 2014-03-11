package example3;

/**
 * This example demonstrates the use of specifications for debugging purposes. 
 * The example uses method contracts and loop invariants specified in the 
 * Java Modeling Language (JML). 
 * <p>
 * To debug method {@link #indexOf(Object[], Object, Comparator)} follow the 
 * instructions:
 * <ol>
 *    <li>Debug method {@link #indexOf(Object[], Object, Comparator)}</li>
 *    <li>Terminate the debug session</li>
 *    <li>
 *       Edit the debug configuration via main menu item 
 *       'Run, Debug Configurations'
 *    </li>
 *    <li>
 *       Select 'Use existing contract', click on 'Browse' and choose the only 
 *       available method contract
 *    </li>
 *    <li>
 *       Debug method {@link #indexOf(Object[], Object, Comparator)} again
 *    </li>
 *    <li>
 *       Select method treatment 'Contract' in view 
 *       'Symbolic Execution Settings'
 *    </li>
 *    <li>
 *       Select loop treatment 'Invariant' in view 'Symbolic Execution Settings'
 *    </li>
 *    <li>Resume execution</li>
 * </ol>
 * Instead of unwinding the loop and inlining a specific implementation of the 
 * interface method 'equals', the loop invariant respective the method contract 
 * is applied. This achieves a finite symbolic execution tree which covers all
 * possible concrete execution paths as long as application is correct. 
 * Problematic applications are indicated by red crossed node icons. 
 *<p>
 * The 'Body Preserves Invariant' branch represents an arbitrary loop iteration. 
 * The red crossed icon in one of its leaves indicates that the loop invariant 
 * might not be preserved. Further inspection reveals that the loop counter 
 * {@code i}is not increased in the then branch.
 * <p>
 * The loop body calls method {@link Comparator#equals(Object, Object)}. Instead 
 * of inlining a specific implementation, the method contract is used. To apply 
 * a method contract, its precondition has to be checked. A failed check is 
 * indicated by a node marker.
 *<p>
 * The 'Use Case' branch continues the symbolic execution in arbitrary state 
 * after loop. A closer look at the 'return' nodes exhibits yet another problem, 
 * namely, the loop counter 'i' is returned instead of variable 'index'.
 */
public class ArrayUtil {
	/*@ normal_behavior
	  @ requires \invariant_for(c);
	  @*/
	public static int /*@ strictly_pure @*/ indexOf(Object[] a, 
	                                                Object s, 
	                                                Comparator c) {
		int index = -1;
		int i = 0;
		/*@ loop_invariant i >= 0 && i <= a.length;
		  @ decreasing a.length - i;
		  @ assignable \strictly_nothing;
		  @*/
		while (index < 0 && i < a.length) {
			if (c.equals(a[i], s)) {
				index = i;
			}
			else {
				i++;
			}
		}
		return i;
	}
	
	public static interface Comparator {
		/*@ normal_behavior
		  @ requires true;
		  @ ensures true;
		  @*/
		public boolean /*@ strictly_pure @*/ equals(/*@ nullable @*/ Object first, 
		                                            /*@ nullable @*/ Object second);
	}
}
