package org.key_project.sed.core.model.impl;

import org.eclipse.debug.internal.ui.viewers.model.provisional.IColumnPresentationFactory;
import org.key_project.sed.core.model.ISEDBaseMethodReturn;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.provider.SEDBaseMethodReturnColumnPresentationFactory;

/**
 * Provides a basic implementation of {@link ISEDBaseMethodReturn}.
 * @author Martin Hentschel
 * @see ISEDBaseMethodReturn
 */
@SuppressWarnings("restriction")
public abstract class AbstractSEDBaseMethodReturn extends AbstractSEDStackFrameCompatibleDebugNode implements ISEDBaseMethodReturn {
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this method return is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEDThread} in that this method return is contained.
    */
   public AbstractSEDBaseMethodReturn(ISEDDebugTarget target, 
                                      ISEDDebugNode parent,
                                      ISEDThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Class adapter) {
      if (IColumnPresentationFactory.class.equals(adapter)) {
         return new SEDBaseMethodReturnColumnPresentationFactory();
      }
      else {
         return super.getAdapter(adapter);
      }
   }
}
