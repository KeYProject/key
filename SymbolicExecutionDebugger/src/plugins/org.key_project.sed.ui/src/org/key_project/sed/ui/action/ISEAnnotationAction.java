package org.key_project.sed.ui.action;

import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.ui.property.AnnotationPropertySection;

/**
 * An action which is executed from the {@link AnnotationPropertySection}.
 * @author Martin Hentschel
 */
public interface ISEAnnotationAction {
   /**
    * Run the action.
    * @param shell The current {@link Shell}.
    * @param target The selected {@link ISEDebugTarget}.
    */
   public void run(Shell shell, ISEDebugTarget target);
}
