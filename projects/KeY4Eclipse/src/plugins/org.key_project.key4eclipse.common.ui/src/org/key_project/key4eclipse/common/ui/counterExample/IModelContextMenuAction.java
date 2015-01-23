package org.key_project.key4eclipse.common.ui.counterExample;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;

import de.uka.ilkd.key.gui.smt.SolverListener.InternSMTProblem;
import de.uka.ilkd.key.smt.model.Model;

/**
 * A context menu action shown in the model tab of a {@link SMTProblemPropertyPage}.
 * @author Martin Hentschel
 */
public interface IModelContextMenuAction {
   /**
    * Initializes the instance with the current state.
    * @param shell The current {@link Shell}.
    * @param problem The {@link InternSMTProblem} which provides the {@link Model}.
    * @param model The {@link Model}.
    * @param selection The current {@link ISelection}.
    */
   public void init(Shell shell, InternSMTProblem problem, Model model, ISelection selection);

   /**
    * Checks if the action is visible.
    * @return {@code true} visible, {@code false} hidden.
    */
   public boolean isVisible();

   /**
    * Returns the text.
    * @return The text.
    */
   public String getText();

   /**
    * Returns the optional {@link ImageDescriptor}.
    * @return The optional {@link ImageDescriptor} or {@code null}.
    */
   public ImageDescriptor getImageDescriptor();

   /**
    * Checks if this action is enabled.
    * @return {@code true} enabled, {@code false} disabled.
    */
   public boolean isEnabled();

   /**
    * Performs the operation.
    */
   public void run();
}
