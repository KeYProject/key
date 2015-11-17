package org.key_project.sed.core.annotation.impl;

import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationAppearance;
import org.key_project.sed.core.annotation.ISEAnnotationType;

/**
 * An {@link ISEAnnotationAppearance} which can be instantiated to define
 * the expected appearance of an {@link ISEAnnotation}.
 * @author Martin Hentschel
 */
public class AnnotationApperanceDefinition extends AbstractSEAnnotationAppearance {
   /**
    * Constructor.
    * @param type The type of this annotation.
    */
   public AnnotationApperanceDefinition(ISEAnnotationType type) {
      super(type);
   }
}
