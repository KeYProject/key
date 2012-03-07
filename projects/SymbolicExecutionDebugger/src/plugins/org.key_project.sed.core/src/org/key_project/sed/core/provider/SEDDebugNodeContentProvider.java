package org.key_project.sed.core.provider;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.internal.ui.model.elements.ElementContentProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementContentProvider;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IPresentationContext;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IViewerUpdate;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * <p>
 * Implementation of {@link IElementContentProvider} that is used to
 * return the children of an {@link ISEDDebugNode}. 
 * </p>
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SEDDebugNodeContentProvider extends ElementContentProvider {
   /**
    * Returns the available children.
    * @param parent The parent element for that the children are needed.
    * @return The children. 
    * @throws CoreException Occurred Exception.
    */
   protected Object[] getChildren(Object parent) throws CoreException {
      if (parent instanceof ISEDDebugNode) {
         Object[] children = ((ISEDDebugNode)parent).getChildren();
         return children != null ? children : new Object[0];
      }
      else {
         return new Object[0];
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Object[] getChildren(Object parent, int index, int length, IPresentationContext context, IViewerUpdate monitor) throws CoreException {
      return getElements(getChildren(parent), index, length);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected int getChildCount(Object element, IPresentationContext context, IViewerUpdate monitor) throws CoreException {
      return getChildren(element).length;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean supportsContextId(String id) {
      return IDebugUIConstants.ID_DEBUG_VIEW.equals(id);
   }
}
