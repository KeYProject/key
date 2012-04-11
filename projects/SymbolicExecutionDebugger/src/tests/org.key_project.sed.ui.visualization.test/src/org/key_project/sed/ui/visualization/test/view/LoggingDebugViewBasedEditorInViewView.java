package org.key_project.sed.ui.visualization.test.view;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.key_project.sed.ui.visualization.view.AbstractDebugViewBasedEditorInViewView;
import org.key_project.util.test.editor.TextControlEditor;

public class LoggingDebugViewBasedEditorInViewView extends AbstractDebugViewBasedEditorInViewView {
   public static final String VIEW_ID = "org.key_project.sed.ui.visualization.test.view.LoggingDebugViewBasedEditorInViewView";
   
   private List<LogEntry> log = new LinkedList<LoggingDebugViewBasedEditorInViewView.LogEntry>();
   
   @Override
   protected boolean shouldHandleDebugView(IDebugView debugView) {
      return IDebugUIConstants.ID_DEBUG_VIEW.equals(debugView.getSite().getId());
   }

   @Override
   protected void handleDebugViewChanged(IDebugView oldDebugView, IDebugView newDebugView) {
      log.add(new LogEntry(oldDebugView, newDebugView));
   }
   
   public LogEntry[] getLog() {
      return log.toArray(new LogEntry[log.size()]);
   }

   public void clearLog() {
      log.clear();
   }

   @Override
   protected IEditorPart createEditorPart() {
      return new TextControlEditor();
   }

   @Override
   protected IEditorActionBarContributor createEditorActionBarContributor() {
      return null;
   }

   @Override
   protected IEditorInput getEditorInput() {
      return null;
   }
   
   public static class LogEntry {
      private IDebugView oldDebugView;

      private IDebugView newDebugView;
      
      public LogEntry(IDebugView oldDebugView, IDebugView newDebugView) {
         super();
         this.oldDebugView = oldDebugView;
         this.newDebugView = newDebugView;
      }
      public IDebugView getOldDebugView() {
         return oldDebugView;
      }
      public IDebugView getNewDebugView() {
         return newDebugView;
      }
   }
}
