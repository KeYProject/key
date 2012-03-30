package org.key_project.sed.core.util;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.util.java.ArrayUtil;

/**
 * <p>
 * Iterates preorder over the whole containment hierarchy of a given {@link ISEDDebugTarget}.
 * </p>
 * <p>
 * Instances of this class should always be used instead of recursive method
 * calls because they cause {@link StackOverflowError}s even in small programs.
 * </p>
 * <p>
 * <b>Attention: </b>The iteration process does not take care of changes in
 * the model. If the containment hierarchy changes during iteration it is possible
 * that elements are left or visited multiple times. For this reason it is forbidden
 * to change the model during iteration. But the developer has to take care about it.
 * </p>
 * @author Martin Hentschel
 */
public class SEDIterator {
   /**
    * The next element or {@code null} if no more elements exists.
    */
   private ISEDDebugElement next;
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} to iterate over.
    */
   public SEDIterator(ISEDDebugTarget target) {
      super();
      this.next = target;
   }
   
   /**
    * Checks if more elements are available.
    * @return {@code true} has more elements, {@code false} has not more elements.
    * @throws DebugException Occurred Exception.
    */
   public boolean hasNext() throws DebugException {
      return next != null;
   }
   
   /**
    * Returns the next {@link ISEDDebugElement} in the containment hierarchy.
    * @return The next {@link ISEDDebugElement}.
    * @throws DebugException Occurred Exception.
    */
   public ISEDDebugElement next() throws DebugException {
      ISEDDebugElement oldNext = next;
      updateNext();
      return oldNext;
   }

   /**
    * Computes the next element and updates {@link #next()}.
    * @throws DebugException Occurred Exception.
    */
   protected void updateNext() throws DebugException {
      ISEDDebugElement newNext = null;
      if (next instanceof ISEDDebugTarget) {
         ISEDDebugTarget target = (ISEDDebugTarget)next;
         ISEDThread[] threads = target.getSymbolicThreads();
         if (!ArrayUtil.isEmpty(threads)) {
            newNext = threads[0];
         }
      }
      else if (next instanceof ISEDDebugNode) {
         ISEDDebugNode node = (ISEDDebugNode)next;
         ISEDDebugNode[] children = node.getChildren();
         if (!ArrayUtil.isEmpty(children)) {
            newNext = children[0];
         }
         else {
            newNext = getNextOnParent(node);
         }
      }
      this.next = newNext;
   }
   
   /**
    * Returns the next element to select if all children of the given
    * {@link ISEDDebugNode} are visited.
    * @param node The visited {@link ISEDDebugNode}.
    * @return The next {@link ISEDDebugElement} to visit.
    * @throws DebugException Occurred Exception.
    */
   protected ISEDDebugElement getNextOnParent(ISEDDebugNode node) throws DebugException {
      if (node instanceof ISEDThread) {
         ISEDDebugTarget parent = node.getDebugTarget();
         ISEDThread[] parentChildren = parent.getSymbolicThreads();
         int nodeIndex = ArrayUtil.indexOf(parentChildren, node);
         if (nodeIndex < 0) {
            throw new DebugException(LogUtil.getLogger().createErrorStatus("Debug target \"" + parent + "\" does not contain thread \"" + node + "."));
         }
         if (nodeIndex + 1 < parentChildren.length) {
            return parentChildren[nodeIndex + 1];
         }
         else {
            return null; // End of model reached.
         }
      }
      else {
         ISEDDebugNode parent = node.getParent();
         if (parent == null) {
            throw new DebugException(LogUtil.getLogger().createErrorStatus("Node \"" + node + "\" has no parent."));
         }
         ISEDDebugNode[] parentChildren = parent.getChildren();
         int nodeIndex = ArrayUtil.indexOf(parentChildren, node);
         if (nodeIndex < 0) {
            throw new DebugException(LogUtil.getLogger().createErrorStatus("Parent node \"" + parent + "\" does not contain child \"" + node + "."));
         }
         if (nodeIndex + 1 < parentChildren.length) {
            return parentChildren[nodeIndex + 1];
         }
         else {
            return getNextOnParent(parent);
         }
      }
   }
}
