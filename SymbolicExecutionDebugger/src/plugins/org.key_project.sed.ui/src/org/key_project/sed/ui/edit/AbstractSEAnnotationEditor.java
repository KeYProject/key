package org.key_project.sed.ui.edit;

import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.util.bean.Bean;

/**
 * Provides a basic implementation of {@link ISEAnnotationEditor}.
 * @author Martin Hentschel
 */
public abstract class AbstractSEAnnotationEditor extends Bean implements ISEAnnotationEditor {
   /**
    * The {@link ISEDebugTarget} in which the {@link ISEAnnotation} is used.
    */
   private ISEDebugTarget target;

   /**
    * The specified {@link ISEAnnotation}.
    */
   private ISEAnnotation annotation;
   
   /**
    * The defined error message.
    */
   private String errorMessage;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void init(ISEDebugTarget target, ISEAnnotation annotation) {
      this.target = target;
      this.annotation = annotation;
   }

   /**
    * Returns the {@link ISEDebugTarget} in which the {@link ISEAnnotation} is used.
    * @return The {@link ISEDebugTarget} in which the {@link ISEAnnotation} is used.
    */
   public ISEDebugTarget getTarget() {
      return target;
   }

   /**
    * Returns the specified {@link ISEAnnotation}.
    * @return The specified {@link ISEAnnotation}.
    */
   protected ISEAnnotation getAnnotation() {
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
