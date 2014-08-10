package org.key_project.key4eclipse.resources.util;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.texteditor.ITextEditor;

public class EditorSelection {
   
   private ISelection activeSelection = null;
   private ITextEditor activeEditor = null;
   private List<ITextEditor> openEditors = new LinkedList<ITextEditor>();
   
   public ISelection getActiveSelection() {
      return activeSelection;
   }
   public void setActiveSelection(ISelection activeSelection) {
      this.activeSelection = activeSelection;
   }
   public ITextEditor getActiveEditor() {
      return activeEditor;
   }
   public void setActiveEditor(ITextEditor activeEditor) {
      this.activeEditor = activeEditor;
   }
   public List<ITextEditor> getOpenEditors() {
      return openEditors;
   }
   public void setOpenEditors(List<ITextEditor> openEditors) {
      this.openEditors = openEditors;
   }
   public void addOpenEditor(ITextEditor openEditor) {
      openEditors.add(openEditor);
   }
   
}
