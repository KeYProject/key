package org.key_project.util.test.editor;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;

/**
 * A simple {@link IEditorPart} which contains one {@link Text} instance.
 * @author Martin Hentschel
 */
public class TextControlEditor extends EditorPart {
   /**
    * The contained {@link Text} instance.
    */
   private Text text;

   /**
    * {@inheritDoc}
    */
   @Override
   public void doSave(IProgressMonitor monitor) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void doSaveAs() {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IEditorSite site, IEditorInput input) throws PartInitException {
      setSite(site);
      if (input != null) {
         setInput(input);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isDirty() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isSaveAsAllowed() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      text = new Text(parent, SWT.BORDER);
      text.setText("This is an Editor.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
      text.setFocus();
   }
}
