package org.key_project.sed.ui.property;

import org.eclipse.ui.views.properties.tabbed.ISection;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.model.ISEDebugTarget;

/**
 * An {@link ISection} implementation to edit the {@link ISEAnnotation}s
 * of an {@link ISEDebugTarget}.
 * @author Martin Hentschel
 */
public class AnnotationLinkPropertySection extends AbstractSENodePropertySection {
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
