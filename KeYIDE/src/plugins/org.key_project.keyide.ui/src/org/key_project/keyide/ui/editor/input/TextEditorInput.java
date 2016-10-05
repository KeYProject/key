package org.key_project.keyide.ui.editor.input;

import org.eclipse.core.resources.IStorage;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.PlatformObject;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IPersistableElement;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.editors.text.TextEditor;
import org.key_project.util.java.StringUtil;

/**
 * An {@link IEditorInput} used to show a given {@link String} in a {@link TextEditor}.
 * @author Martin Hentschel
 */
public class TextEditorInput extends PlatformObject implements IStorageEditorInput {
   /**
    * The {@link IStorage} which is used by {@link TextEditor}s to show the initial content.
    */
   private final IStorage storage;
   
   /**
    * Constructor.
    * @param text The text to show.
    * @param name The name to use.
    */
   public TextEditorInput(String text, String name) {
      storage = new TextStorage(text, 
                                StringUtil.chop(name, 30)); // The name can't be longer than roughly 30 characters because otherwise the rendering of an IEditorPart will be really slow.
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean exists() {
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
   public String getName() {
      return storage.getName();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IPersistableElement getPersistable() {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getToolTipText() {
      return "String-based file: " + storage.getName();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IStorage getStorage() throws CoreException {
      return storage;
   }
}