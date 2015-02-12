package org.key_project.key4eclipse.resources.ui.provider;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.viewers.AbstractTableViewer;
import org.eclipse.jface.viewers.ILazyContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.key_project.key4eclipse.resources.log.LogManager;
import org.key_project.key4eclipse.resources.log.LogRecord;

/**
 * An {@link ILazyContentProvider} to show {@link LogRecord}s lazily.
 * @author Martin Hentschel
 */
public class LogRecordLazyContentProvider implements ILazyContentProvider {
   /**
    * The {@link AbstractTableViewer} in which this {@link ILazyContentProvider} is used.
    */
   private AbstractTableViewer viewer;
   
   /**
    * The {@link IProject} for which the log records are shown.
    */
   private IProject project;

   /**
    * Optionally the {@link Exception} occurred during counting the number of log records.
    */
   private Exception countException;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
      Assert.isTrue(viewer instanceof AbstractTableViewer);
      this.viewer = (AbstractTableViewer) viewer;
      if (newInput instanceof IProject) {
         this.project = (IProject) newInput;
         try {
            this.viewer.setItemCount((int)LogManager.getInstance().countRecords(project));
         }
         catch (Exception e) {
            countException = e;
            this.viewer.setItemCount(1);
         }
      }
      else {
         this.project = null;
         this.countException = null;
         this.viewer.setItemCount(0);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateElement(int index) {
      try {
         if (this.countException != null) {
            viewer.replace(countException, index);
         }
         else {
            LogRecord record = LogManager.getInstance().readRecord(project, index);
            viewer.replace(record, index);
         }
      }
      catch (Exception e) {
         viewer.replace(e, index);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
   }
}
