package org.key_project.util.test.editor;

import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.key_project.util.eclipse.view.editorInView.IGlobalEnablement;

/**
 * {@link IEditorActionBarContributor} for {@link TextControlEditor} instances.
 * @author Martin Hentschel
 */
public class TextControlEditorContributor implements IEditorActionBarContributor, IGlobalEnablement {
   /**
    * The global enabled.
    */
   private boolean globalEnabled;

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IActionBars bars, IWorkbenchPage page) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setActiveEditor(IEditorPart targetEditor) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGlobalEnabled() {
      return globalEnabled;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setGlobalEnabled(boolean globalEnabled) {
      this.globalEnabled = globalEnabled;
   }
}
