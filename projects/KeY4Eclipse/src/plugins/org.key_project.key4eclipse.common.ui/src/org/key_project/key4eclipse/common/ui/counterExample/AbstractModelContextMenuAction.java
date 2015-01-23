package org.key_project.key4eclipse.common.ui.counterExample;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;

import de.uka.ilkd.key.gui.smt.SolverListener.InternSMTProblem;
import de.uka.ilkd.key.smt.model.Model;

/**
 * Provides a default implementation of {@link IModelContextMenuAction}.
 * @author Martin Hentschel
 */
public abstract class AbstractModelContextMenuAction implements IModelContextMenuAction {
   /**
    * The current {@link Shell}.
    */
   private Shell shell;

   /**
    * The {@link InternSMTProblem} which provides the model.
    */
   private InternSMTProblem problem;
   
   /**
    * The {@link Model}.
    */
   private Model model;

   /**
    * The current {@link ISelection}.
    */
   private ISelection selection;

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(Shell shell, InternSMTProblem problem, Model model, ISelection selection) {
      this.shell = shell;
      this.problem = problem;
      this.model = model;
      this.selection = selection;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isVisible() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImageDescriptor getImageDescriptor() {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isEnabled() {
      return true;
   }

   /**
    * Returns the current {@link Shell}.
    * @return The current {@link Shell}.
    */
   public Shell getShell() {
      return shell;
   }

   /**
    * Returns the {@link InternSMTProblem} which provides the model.
    * @return The {@link InternSMTProblem} which provides the model.
    */
   protected InternSMTProblem getProblem() {
      return problem;
   }

   /**
    * Returns the {@link Model}.
    * @return The {@link Model}.
    */
   protected Model getModel() {
      return model;
   }

   /**
    * Returns the current {@link ISelection}.
    * @return The current {@link ISelection}.
    */
   protected ISelection getSelection() {
      return selection;
   }
}
