package org.key_project.sed.core.annotation.impl;

import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.util.SEAnnotationUtil;

/**
 * The {@link ISEAnnotation} representing breakpoints.
 * @author Martin Hentschel
 * @see BreakpointAnnotationType
 */
public class BreakpointAnnotation extends AbstractSEAnnotation {   
   /**
    * Constructor.
    */
   public BreakpointAnnotation() {
      super(SEAnnotationUtil.getAnnotationtype(BreakpointAnnotationType.TYPE_ID), true);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canDelete(ISEDebugTarget target) {
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
