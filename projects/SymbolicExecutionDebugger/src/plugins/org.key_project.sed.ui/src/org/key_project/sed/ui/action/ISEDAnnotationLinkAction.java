package org.key_project.sed.ui.action;

import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.property.AnnotationLinkTabComposite;

/**
 * An action which is executed from the {@link AnnotationLinkTabComposite}.
 * @author Martin Hentschel
 */
public interface ISEDAnnotationLinkAction {
   /**
    * Run the action.
    * @param shell The current {@link Shell}.
    * @param node The selected {@link ISEDDebugNode}.
    */
   public void run(Shell shell, ISEDDebugNode node);
}
