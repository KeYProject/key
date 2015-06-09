package org.key_project.javaeditor.outline;

import org.eclipse.jdt.internal.ui.javaeditor.JavaOutlinePage;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

/**
 * The {@link ITreeContentProvider} which allows to modify
 * the original content provided in the {@link JavaOutlinePage}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class OutlineContentProviderWrapper implements ITreeContentProvider {
   /**
    * The original {@link ITreeContentProvider} of a {@link JavaOutlinePage}.
    */
   private ITreeContentProvider originalProvider;
   
   /**
    * Constructor.
    * @param originalProvider The original {@link ITreeContentProvider} of a {@link JavaOutlinePage}.
    */
   public OutlineContentProviderWrapper(ITreeContentProvider originalProvider) {
      this.originalProvider = originalProvider;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      originalProvider.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
      originalProvider.inputChanged(viewer, oldInput, newInput);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object[] getElements(Object inputElement) {
      Object[] elements = originalProvider.getElements(inputElement);
      return elements;
//      return new Object[] {elements[0], ""};
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object[] getChildren(Object parentElement) {
      return originalProvider.getChildren(parentElement);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object getParent(Object element) {
      return originalProvider.getParent(element);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasChildren(Object element) {
      return originalProvider.hasChildren(element);
   }

   /**
    * Returns the original {@link ITreeContentProvider} of a {@link JavaOutlinePage}.
    * @return The original {@link ITreeContentProvider} of a {@link JavaOutlinePage}.
    */
   public ITreeContentProvider getOriginalProvider() {
      return originalProvider;
   }
}
