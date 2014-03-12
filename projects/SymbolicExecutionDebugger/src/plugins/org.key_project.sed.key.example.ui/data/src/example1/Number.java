package example1;

/**
 * To debug method {@link #eq(Number)} symbolically with the 
 * Symbolic Execution Debugger (SED) follow the steps below:
 * <ol>
 *    <li>Select method {@link #eq(Number)}</li>
 *    <li>
 *       Select context menu item 'Debug As, Symbolic Execution Debugger (SED)'
 *    </li>
 *    <li>Confirm switch to perspective 'Symbolic Debug'</li>
 *    <li>
 *       In view 'Debug', click on 'Resume' to start symbolic execution 
 *       (stepwise symbolic execution and breakpoints are also supported)
 *    </li>
 * </ol>
 * <p>
 * After symbolic execution has finished, a so called symbolic execution tree is 
 * shown in view 'Symbolic Execution Tree'. A symbolic execution tree contains 
 * all possible execution paths up to the reached depth. Each path may represent 
 * infinitely many concrete execution paths.
 * <p>
 * Selecting a node highlights the related source code. The 'Properties' view 
 * provides additional information like the symbolic method call stack or the 
 * path condition. The path condition expresses the necessary constraints on the 
 * initial state which must be satisfied to reach the current node.
 * <p>
 * View 'Variables' shows the symbolic state of a node; only locations accessed 
 * during symbolic execution are listed.
 */
public class Number {
   private int value;
	
   public boolean eq(Number n) {
      if (value == n.value) {
         return true;
      }
      else {
         return false;
      }
   }
}
