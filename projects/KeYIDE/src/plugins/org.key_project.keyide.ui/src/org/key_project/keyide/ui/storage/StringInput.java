package org.key_project.keyide.ui.storage;

import org.eclipse.core.resources.IStorage;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IPersistableElement;
import org.eclipse.ui.IStorageEditorInput;

public class StringInput implements IStorageEditorInput{
   
   private IStorage storage;
   
   public StringInput(IStorage storage){
      this.storage=storage;
   }

   @Override
   public boolean exists() {
      return true;
   }

   @Override
   public ImageDescriptor getImageDescriptor() {
      return null;
   }

   @Override
   public String getName() {
      return storage.getName();
   }

   @Override
   public IPersistableElement getPersistable() {
      return null;
   }

   @Override
   public String getToolTipText() {
      return "String-based file: " + storage.getName();
   }

   @Override
   public Object getAdapter(Class adapter) {
      return null;
   }

   @Override
   public IStorage getStorage() throws CoreException {
      return storage;
   }

}
