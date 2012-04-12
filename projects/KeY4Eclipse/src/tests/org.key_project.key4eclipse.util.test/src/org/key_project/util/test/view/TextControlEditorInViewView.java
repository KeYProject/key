package org.key_project.util.test.view;

import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorInput;
import org.key_project.util.eclipse.view.editorInView.AbstractEditorInViewView;
import org.key_project.util.test.editor.TextControlEditor;

/**
 * Contains a {@link TextControlEditor} instance but shows by default
 * a message.
 * @author Martin Hentschel
 */
public class TextControlEditorInViewView extends AbstractEditorInViewView<TextControlEditor> {
   /**
    * The ID of this view.
    */
   public static final String VIEW_ID = "org.key_project.util.test.view.TextControlEditorInViewView";

   /**
    * Constructor.
    */
   public TextControlEditorInViewView() {
      setMessage("Initial message from TextControlEditorInViewView.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected TextControlEditor createEditorPart() {
      return new TextControlEditor();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IEditorActionBarContributor createEditorActionBarContributor() {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IEditorInput createEditorInput() {
      return null;
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public void setMessage(String message) {
      super.setMessage(message);
   }
}
