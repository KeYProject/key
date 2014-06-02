package org.key_project.sed.ui.edit;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.util.bean.IBean;

/**
 * An editor used to edit {@link ISEDAnnotation}s.
 * @author Martin Hentschel
 */
public interface ISEDAnnotationEditor extends IBean {
   /**
    * Property {@link #getErrorMessage()}.
    */
   public static final String PROP_ERROR_MESSAGE = "errorMessage";
   
   /**
    * Defines the {@link ISEDAnnotation} to edit.
    * @param target {@link ISEDDebugTarget} in which the {@link ISEDAnnotation} is used.
    * @param annotation The {@link ISEDAnnotation} to edit.
    */
   public void init(ISEDDebugTarget target, ISEDAnnotation annotation);
   
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
    * Applies the changes to the {@link ISEDAnnotation}.
    * @param monitor The {@link IProgressMonitor} to use only available if {@link #needsProgressMonitor(IProgressMonitor)} returns {@code true}.
    */
   public void applyChanges(IProgressMonitor monitor) throws Exception;
   
   /**
    * Checks if an {@link IProgressMonitor} is needed.
    * @return {@code true} needs {@link IProgressMonitor}, {@code false} does not need {@link IProgressMonitor}.
    */
   public boolean needsProgressMonitor();
}
