package org.key_project.sed.core.annotation.impl;

import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationAppearance;
import org.key_project.sed.core.annotation.ISEDAnnotationType;

/**
 * An {@link ISEDAnnotationAppearance} which can be instantiated to define
 * the expected appearance of an {@link ISEDAnnotation}.
 * @author Martin Hentschel
 */
public class AnnotationApperanceDefinition extends AbstractSEDAnnotationAppearance {
   /**
    * Constructor.
    * @param type The type of this annotation.
    */
   public AnnotationApperanceDefinition(ISEDAnnotationType type) {
      super(type);
   }
}
