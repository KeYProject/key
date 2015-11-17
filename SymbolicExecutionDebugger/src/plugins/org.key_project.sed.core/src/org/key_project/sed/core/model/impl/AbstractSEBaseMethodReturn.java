package org.key_project.sed.core.model.impl;

import org.eclipse.debug.internal.ui.viewers.model.provisional.IColumnPresentationFactory;
import org.key_project.sed.core.model.ISEBaseMethodReturn;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.provider.SEBaseMethodReturnColumnPresentationFactory;

/**
 * Provides a basic implementation of {@link ISEBaseMethodReturn}.
 * @author Martin Hentschel
 * @see ISEBaseMethodReturn
 */
@SuppressWarnings("restriction")
public abstract class AbstractSEBaseMethodReturn extends AbstractSEStackFrameCompatibleDebugNode implements ISEBaseMethodReturn {
   /**
    * Constructor.
    * @param target The {@link ISEDebugTarget} in that this method return is contained.
    * @param parent The parent in that this node is contained as child.
    * @param thread The {@link ISEThread} in that this method return is contained.
    */
   public AbstractSEBaseMethodReturn(ISEDebugTarget target, 
                                      ISENode parent,
                                      ISEThread thread) {
      super(target, parent, thread);
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Class adapter) {
      if (IColumnPresentationFactory.class.equals(adapter)) {
         return new SEBaseMethodReturnColumnPresentationFactory();
      }
      else {
         return super.getAdapter(adapter);
      }
   }
}
