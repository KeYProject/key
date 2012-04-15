package org.key_project.sed.core.model.impl;

import org.eclipse.core.runtime.Platform;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementContentProvider;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.provider.SEDDebugNodeContentProvider;

/**
 * Provides a basic implementation of {@link ISEDDebugNode}.
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
@SuppressWarnings("restriction")
public abstract class AbstractSEDDebugNode extends AbstractSEDDebugElement implements ISEDDebugNode {
   /**
    * The parent in that this node is contained as child.
    */
   private ISEDDebugNode parent;
   
   /**
    * The name of this debug node.
    */
   private String name;
   
   /**
    * The thread.
    */
   private ISEDThread thread;
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this node is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this node is contained.
    */
   public AbstractSEDDebugNode(ISEDDebugTarget target, 
                               ISEDDebugNode parent, 
                               ISEDThread thread) {
      super(target);
      this.parent = parent;
      this.thread = thread;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugNode getParent() throws DebugException {
      return parent;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDThread getThread() {
      return thread;
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Class adapter) {
      if (IElementContentProvider.class.equals(adapter)) {
         // Change used content provider to show SED specific children instead of the default one from the debug API.
         return SEDDebugNodeContentProvider.getDefaultInstance();
      }
      else {
         return Platform.getAdapterManager().getAdapter(this, adapter);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() throws DebugException {
      return name;
   }

   /**
    * Sets the name of this node.
    * @param name the name to set.
    */
   protected void setName(String name) {
      this.name = name;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      try {
         return getNodeType() + ": " + getName();
      }
      catch (DebugException e) {
         return e.getMessage();
      }
   }
}
