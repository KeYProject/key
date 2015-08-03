package org.key_project.key4eclipse.resources.builder;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.IMethod;

/**
 * Stores the current state of the editor. Includes open files, active/selected file and the selected method within the active file.
 * @author Stefan Käsdorf
 */
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
