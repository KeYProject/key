package org.key_project.key4eclipse.resources.util;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.text.ITextSelection;

public class EditorSelection {
   
   private ITextSelection activeSelection = null;
   private IFile activeFile = null;
   private List<IFile> openFiles = new LinkedList<IFile>();
   
   public ITextSelection getActiveSelection() {
      return activeSelection;
   }
   public void setActiveSelection(ITextSelection activeSelection) {
      this.activeSelection = activeSelection;
   }
   
   public IFile getActiveFile(){
      return activeFile;
   }
   public void setActiveFile(IFile activeFile){
      this.activeFile = activeFile;
   }
   
   public List<IFile> getOpenFiles() {
      return openFiles;
   }
   public void addOpenFile(IFile openFile) {
      openFiles.add(openFile);
   }
   
}
