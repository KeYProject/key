package org.key_project.sed.ui.action;

import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.ui.property.AnnotationLinkTabComposite;

/**
 * An action which is executed from the {@link AnnotationLinkTabComposite}.
 * @author Martin Hentschel
 */
public interface ISEAnnotationLinkAction {
   /**
    * Run the action.
    * @param shell The current {@link Shell}.
    * @param node The selected {@link ISENode}.
    */
   public void run(Shell shell, ISENode node);
}
