package org.key_project.sed.ui.action;

import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.ui.property.AnnotationLinkTabComposite;

/**
 * An edit action which is executed from the {@link AnnotationLinkTabComposite}.
 * @author Martin Hentschel
 */
public interface ISEAnnotationLinkEditAction {
   /**
    * Checks if the given {@link ISEAnnotationLink} can be edited.
    * @param link The {@link ISEAnnotationLink} to check.
    * @return {@code true} edit possible, {@code false} edit not possible.
    */
   public boolean canEdit(ISEAnnotationLink link);
   
   /**
    * Edits the given {@link ISEAnnotationLink}.
    * @param shell The currently active {@link Shell}.
    * @param link The {@link ISEAnnotationLink} to edit.
    */
   public void edit(Shell shell, ISEAnnotationLink link);
}
