package org.key_project.sed.ui.text;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.texteditor.IAnnotationImageProvider;

/**
 * The {@link IAnnotationImageProvider} of {@link SymbolicallyReachedAnnotation}s.
 * @author Martin Hentschel
 */
public class SymbolicallyReachedAnnotationImageProvider implements IAnnotationImageProvider {
   /**
    * {@inheritDoc}
    */
   @Override
   public Image getManagedImage(Annotation annotation) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getImageDescriptorId(Annotation annotation) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImageDescriptor getImageDescriptor(String imageDescritporId) {
      return null;
   }
}
