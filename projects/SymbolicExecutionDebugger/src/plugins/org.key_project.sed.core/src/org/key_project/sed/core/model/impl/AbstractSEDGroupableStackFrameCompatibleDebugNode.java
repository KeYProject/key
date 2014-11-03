package org.key_project.sed.core.model.impl;

import org.eclipse.debug.core.DebugEvent;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDGroupable;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Provides a basic implementation of {@link ISEDDebugNode}s which
 * also realize the interface {@link ISEDGroupable}.
 * @author Martin Hentschel
 */
public abstract class AbstractSEDGroupableStackFrameCompatibleDebugNode extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDGroupable {
   /**
    * The collapsed state.
    */
   private boolean collapsed;

   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this method call is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this method call is contained.
    */
   public AbstractSEDGroupableStackFrameCompatibleDebugNode(ISEDDebugTarget target, 
                                                            ISEDDebugNode parent,
                                                            ISEDThread thread) {
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
         fireChangeEvent(DebugEvent.CONTENT);
      }
   }
}
