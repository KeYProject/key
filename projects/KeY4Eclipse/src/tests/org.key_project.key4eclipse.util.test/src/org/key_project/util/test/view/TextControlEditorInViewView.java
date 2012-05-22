package org.key_project.util.test.view;

import org.eclipse.ui.IEditorInput;
import org.key_project.util.eclipse.view.editorInView.AbstractEditorInViewView;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;
import org.key_project.util.test.editor.TextControlEditor;
import org.key_project.util.test.editor.TextControlEditorContributor;

/**
 * Contains a {@link TextControlEditor} instance but shows by default
 * a message.
 * @author Martin Hentschel
 */
public class TextControlEditorInViewView extends AbstractEditorInViewView<TextControlEditor, TextControlEditorContributor> {
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
   protected TextControlEditorContributor createEditorActionBarContributor() {
      return new TextControlEditorContributor();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IEditorInput createEditorInput() {
      return null;
   }
   
   /**
    * Checks if {@link #getEditorComposite()} is enabled or not.
    * @return {@code true} enabled, {@code false} disabled.
    */
   public boolean isEditorCompositeEnabled() {
      IRunnableWithResult<Boolean> run = new AbstractRunnableWithResult<Boolean>() {
         @Override
         public void run() {
            setResult(getEditorComposite().isEnabled());
         }
      };
      getEditorComposite().getDisplay().syncExec(run);
      return run.getResult() != null && run.getResult().booleanValue();
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

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public TextControlEditor getEditorPart() {
      return super.getEditorPart();
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
   public TextControlEditorContributor getEditorActionBarContributor() {
      return (TextControlEditorContributor)super.getEditorActionBarContributor();
   }
}
