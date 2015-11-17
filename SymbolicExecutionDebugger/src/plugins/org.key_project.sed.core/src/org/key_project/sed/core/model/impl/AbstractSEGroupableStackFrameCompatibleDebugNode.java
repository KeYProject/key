package org.key_project.sed.core.model.impl;

import org.eclipse.debug.core.DebugEvent;
import org.eclipse.debug.core.model.DebugElement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEGroupable;
import org.key_project.sed.core.model.ISEThread;

/**
 * Provides a basic implementation of {@link ISENode}s which
 * also realize the interface {@link ISEGroupable}.
 * @author Martin Hentschel
 */
public abstract class AbstractSEGroupableStackFrameCompatibleDebugNode extends AbstractSEStackFrameCompatibleDebugNode implements ISEGroupable {
   /**
    * The collapsed state.
    */
   private boolean collapsed;

   /**
    * Constructor.
    * @param target The {@link ISEDebugTarget} in that this method call is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEThread} in that this method call is contained.
    */
   public AbstractSEGroupableStackFrameCompatibleDebugNode(ISEDebugTarget target, 
                                                            ISENode parent,
                                                            ISEThread thread) {
      super(target, parent, thread);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isCollapsed() {
      return collapsed;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setCollapsed(boolean collapsed) {
      if (this.collapsed != collapsed) {
         this.collapsed = collapsed;
         ((DebugElement) getThread()).fireChangeEvent(DebugEvent.CONTENT);
      }
   }
}
