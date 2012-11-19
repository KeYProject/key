package org.key_project.keyide.ui.storage;

import java.io.InputStream;
import java.io.ByteArrayInputStream;
import org.eclipse.core.resources.IStorage;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;

public class StringStorage implements IStorage {
   
   private String proofString;
   private String name;
   
   public StringStorage(String input, String name){
      this.proofString=input;
      this.name=name;
   }

   @Override
   public Object getAdapter(Class adapter) {
      return null;
   }

   @Override
   public InputStream getContents() throws CoreException {
      return new ByteArrayInputStream(proofString.getBytes());
   }

   @Override
   public IPath getFullPath() {
      return null;
   }

   @Override
   public String getName() {
      return name;
   }

   @Override
   public boolean isReadOnly() {
      return true;
   }

}
