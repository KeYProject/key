package org.key_project.sed.ui.edit;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.util.bean.IBean;

/**
 * An editor used to edit {@link ISEAnnotation}s.
 * @author Martin Hentschel
 */
public interface ISEAnnotationEditor extends IBean {
   /**
    * Property {@link #getErrorMessage()}.
    */
   public static final String PROP_ERROR_MESSAGE = "errorMessage";
   
   /**
    * Defines the {@link ISEAnnotation} to edit.
    * @param target {@link ISEDebugTarget} in which the {@link ISEAnnotation} is used.
    * @param annotation The {@link ISEAnnotation} to edit.
    */
   public void init(ISEDebugTarget target, ISEAnnotation annotation);
   
   /**
    * Creates the editor controls.
    * @param parent The parent {@link Composite}.
    * @return The root of all created edit controls.
    */
   public Control createContent(Composite parent);
   
   /**
    * Returns the error message.
    * @return The error message or {@code null} if everything is valid.
    */
   public String getErrorMessage();
   
   /**
    * Applies the changes to the {@link ISEAnnotation}.
    * @param monitor The {@link IProgressMonitor} to use only available if {@link #needsProgressMonitor(IProgressMonitor)} returns {@code true}.
    */
   public void applyChanges(IProgressMonitor monitor) throws Exception;
   
   /**
    * Checks if an {@link IProgressMonitor} is needed.
    * @return {@code true} needs {@link IProgressMonitor}, {@code false} does not need {@link IProgressMonitor}.
    */
   public boolean needsProgressMonitor();
}
