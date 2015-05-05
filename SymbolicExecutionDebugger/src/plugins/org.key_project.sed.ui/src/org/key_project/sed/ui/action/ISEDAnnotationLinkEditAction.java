package org.key_project.sed.ui.action;

import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.ui.property.AnnotationLinkTabComposite;

/**
 * An edit action which is executed from the {@link AnnotationLinkTabComposite}.
 * @author Martin Hentschel
 */
public interface ISEDAnnotationLinkEditAction {
   /**
    * Checks if the given {@link ISEDAnnotationLink} can be edited.
    * @param link The {@link ISEDAnnotationLink} to check.
    * @return {@code true} edit possible, {@code false} edit not possible.
    */
   public boolean canEdit(ISEDAnnotationLink link);
   
   /**
    * Edits the given {@link ISEDAnnotationLink}.
    * @param shell The currently active {@link Shell}.
    * @param link The {@link ISEDAnnotationLink} to edit.
    */
   public void edit(Shell shell, ISEDAnnotationLink link);
}
