package org.key_project.sed.core.annotation.impl;

import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.util.SEDAnnotationUtil;

/**
 * The {@link ISEDAnnotation} representing breakpoints.
 * @author Martin Hentschel
 * @see BreakpointAnnotationType
 */
public class BreakpointAnnotation extends AbstractSEDAnnotation {   
   /**
    * Constructor.
    */
   public BreakpointAnnotation() {
      super(SEDAnnotationUtil.getAnnotationtype(BreakpointAnnotationType.TYPE_ID), true);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canDelete(ISEDDebugTarget target) {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return getType().getName();
   }
}
