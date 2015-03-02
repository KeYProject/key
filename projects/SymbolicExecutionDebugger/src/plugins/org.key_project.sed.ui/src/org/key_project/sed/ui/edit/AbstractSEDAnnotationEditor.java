package org.key_project.sed.ui.edit;

import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.util.bean.Bean;

/**
 * Provides a basic implementation of {@link ISEDAnnotationEditor}.
 * @author Martin Hentschel
 */
public abstract class AbstractSEDAnnotationEditor extends Bean implements ISEDAnnotationEditor {
   /**
    * The {@link ISEDDebugTarget} in which the {@link ISEDAnnotation} is used.
    */
   private ISEDDebugTarget target;

   /**
    * The specified {@link ISEDAnnotation}.
    */
   private ISEDAnnotation annotation;
   
   /**
    * The defined error message.
    */
   private String errorMessage;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void init(ISEDDebugTarget target, ISEDAnnotation annotation) {
      this.target = target;
      this.annotation = annotation;
   }

   /**
    * Returns the {@link ISEDDebugTarget} in which the {@link ISEDAnnotation} is used.
    * @return The {@link ISEDDebugTarget} in which the {@link ISEDAnnotation} is used.
    */
   public ISEDDebugTarget getTarget() {
      return target;
   }

   /**
    * Returns the specified {@link ISEDAnnotation}.
    * @return The specified {@link ISEDAnnotation}.
    */
   protected ISEDAnnotation getAnnotation() {
      return annotation;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getErrorMessage() {
      return errorMessage;
   }

   /**
    * Sets the error message.
    * @param errorMessage The error message to set.
    */
   protected void setErrorMessage(String errorMessage) {
      String oldMessage = getErrorMessage();
      this.errorMessage = errorMessage;
      firePropertyChange(PROP_ERROR_MESSAGE, oldMessage, getErrorMessage());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean needsProgressMonitor() {
      return false;
   }
}
