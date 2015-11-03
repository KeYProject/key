package org.key_project.javaeditor.outline;

import org.eclipse.jdt.core.ElementChangedEvent;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IElementChangedListener;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.internal.ui.javaeditor.JavaOutlinePage;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.key_project.javaeditor.util.ExtendableOutlineUtil;
import org.key_project.javaeditor.util.PreferenceUtil;
import org.key_project.util.java.ArrayUtil;

/**
 * The {@link ITreeContentProvider} which allows to modify the original content provided in
 * the {@link JavaOutlinePage}.
 * 
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class OutlineContentProviderWrapper implements ITreeContentProvider {
   /**
    * The original {@link ITreeContentProvider} of a {@link JavaOutlinePage}.
    */
   private final ITreeContentProvider originalProvider;
   
   /**
    * The {@link JavaOutlinePage} in which {@link #originalProvider} and this instance is used.
    */
   private final JavaOutlinePage javaOutlinePage;

   /**
    * The {@link TreeViewer} of {@link #javaOutlinePage}.
    */
   private final TreeViewer outlineViewer;

   /**
    * The available {@link IOutlineModifier}.
    */
   private final IOutlineModifier[] outlineModifier = ExtendableOutlineUtil.createEnabledJavaExtensions();

   /**
    * Listens for changes on {@link JavaCore}.
    */
   private final IElementChangedListener changedListener = new IElementChangedListener() {
      @Override
      public void elementChanged(ElementChangedEvent event) {
         handleElementChanged(event);
      }
   };
   
   /**
    * Constructor.
    * @param originalProvider The original {@link ITreeContentProvider} of a {@link JavaOutlinePage}.
    * @param javaOutlinePage The {@link JavaOutlinePage} in which {@link #originalProvider} and this instance is used.
    */
   public OutlineContentProviderWrapper(ITreeContentProvider originalProvider, JavaOutlinePage javaOutlinePage, TreeViewer outlineViewer) {
      this.originalProvider = originalProvider;
      this.javaOutlinePage = javaOutlinePage;
      this.outlineViewer = outlineViewer;
      JavaCore.addElementChangedListener(changedListener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public final void dispose() {
      JavaCore.removeElementChangedListener(changedListener);
      originalProvider.dispose();
   }

   protected void handleElementChanged(final ElementChangedEvent event) {
      // only update if it is extendable in properties
      if (PreferenceUtil.isExtensionsEnabled()){
         if (event.getDelta().getElement() instanceof ICompilationUnit) {
            // update only if change is in ICompilationUnit and all of the changes happened to a comment
            // check for length == 0 makes sure that no outline update is triggered by JDT.
            if (event.getDelta().getAffectedChildren().length == 0 && event.getDelta().getAnnotationDeltas().length == 0 && event.getDelta().getChangedChildren().length == 0) {
                if (outlineViewer != null && !outlineViewer.getControl().isDisposed()) {
                   outlineViewer.getControl().getDisplay().asyncExec(new Runnable() { // Needs to be asynchronously because the UI waits for the compilation reconciler which triggers this event. Otherwise deadlocks are possible.
                     @Override
                     public void run() {
                        //refresh outline with Content
                        if (outlineViewer != null && !outlineViewer.getControl().isDisposed()) {
                           changeDetected(event);
                           outlineViewer.refresh(true);
                        }
                     }
                  });
                }
            }
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public final void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
      originalProvider.inputChanged(viewer, oldInput, newInput);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public final Object[] getElements(Object inputElement) {
      Object[] elements = originalProvider.getElements(inputElement);
      for (IOutlineModifier modifyer : outlineModifier) {
         elements = modifyer.modify(inputElement, elements, javaOutlinePage);
      }
      return elements;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public final Object[] getChildren(Object parentElement) {
      Object[] elements = originalProvider.getChildren(parentElement);
      for (IOutlineModifier modifyer : outlineModifier) {
         elements = modifyer.modify(parentElement, elements, javaOutlinePage);
      }
      return elements;
   }

   /**
    * When a change is detected.
    * @param event The {@link ElementChangedEvent}.
    */
   public void changeDetected(ElementChangedEvent event) {
      for (IOutlineModifier modifyer : outlineModifier) {
         modifyer.changeDetected(event);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public final Object getParent(Object element) {
      return originalProvider.getParent(element);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public final boolean hasChildren(Object element) {
      return !ArrayUtil.isEmpty(getChildren(element));
   }

   /**
    * Returns the original {@link ITreeContentProvider} of a {@link JavaOutlinePage}.
    * 
    * @return The original {@link ITreeContentProvider} of a {@link JavaOutlinePage}.
    */
   public final ITreeContentProvider getOriginalProvider() {
      return originalProvider;
   }
}
