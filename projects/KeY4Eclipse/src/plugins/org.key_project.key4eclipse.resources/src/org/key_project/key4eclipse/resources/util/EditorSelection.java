package org.key_project.key4eclipse.resources.util;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.IMethod;

public class EditorSelection {
   private IMethod selectedMethod;
   private IFile activeFile;
   private final List<IFile> openFiles;
   
   public EditorSelection(){
      this.selectedMethod = null;
      this.activeFile = null;
      this.openFiles = new LinkedList<IFile>();
   }
      
   public IMethod getSelectedMethod() {
      return selectedMethod;
   }
   public void setSelectedMethod(IMethod selectedMethod) {
      this.selectedMethod = selectedMethod;
   }
   
   public IFile getActiveFile() {
      return activeFile;
   }

   public void setActiveFile(IFile activeFile) {
      this.activeFile = activeFile;
   }

   public List<IFile> getOpenFiles() {
      return openFiles;
   }
   public void addOpenFile(IFile openFile) {
      openFiles.add(openFile);
   }
}
