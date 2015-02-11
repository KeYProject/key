package org.key_project.sed.ui.property;

import org.eclipse.ui.views.properties.tabbed.ISection;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugTarget;

/**
 * An {@link ISection} implementation to edit the {@link ISEDAnnotation}s
 * of an {@link ISEDDebugTarget}.
 * @author Martin Hentschel
 */
public class AnnotationLinkPropertySection extends AbstractSEDDebugNodePropertySection {
   /**
    * {@inheritDoc}
    */
   @Override
   protected AnnotationLinkTabComposite createContent() {
      return new AnnotationLinkTabComposite();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean shouldUseExtraSpace() {
      return true;
   }
}
