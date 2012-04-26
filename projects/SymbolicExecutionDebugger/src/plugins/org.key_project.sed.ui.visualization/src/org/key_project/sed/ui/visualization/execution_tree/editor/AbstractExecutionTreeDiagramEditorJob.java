package org.key_project.sed.ui.visualization.execution_tree.editor;

import org.eclipse.core.runtime.jobs.Job;
import org.key_project.util.eclipse.job.ObjectchedulingRule;
import org.key_project.util.java.ObjectUtil;

/**
 * Abstract super class for {@link Job}s executed in an {@link ExecutionTreeDiagramEditor}
 * which have to be executed in serial order. 
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionTreeDiagramEditorJob extends Job {
   /**
    * The {@link ExecutionTreeDiagramEditor} which has executed this {@link Job}.
    */
   private ExecutionTreeDiagramEditor editor;
   
   /**
    * Constructor.
    * @param name The name of this {@link Job}.
    * @param editor The {@link ExecutionTreeDiagramEditor} which has executed this {@link Job}.
    */
   public AbstractExecutionTreeDiagramEditorJob(String name, ExecutionTreeDiagramEditor editor) {
      super(name);
      this.editor = editor;
      setRule(new ObjectchedulingRule(editor));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean belongsTo(Object family) {
      if (ObjectUtil.equals(editor, family)) {
         return true;
      }
      else {
         return super.belongsTo(family);
      }
   }
   
   /**
    * Cancels all {@link Job}s which does something with the given editor.
    * @param editor The editor to cancel his {@link Job}s.
    * @return The canceled {@link Job}s.
    */
   public static Job[] cancelJobs(ExecutionTreeDiagramEditor editor) {
      Job[] jobs = getJobs(editor);
      if (jobs != null) {
         for (Job job : jobs) {
            job.cancel();
         }
      }
      return jobs;
   }
   
   /**
    * Returns all {@link Job}s that does something with the given editor.
    * @param editor The editor.
    * @return The {@link Job}s that does something with the given editor.
    */
   public static Job[] getJobs(ExecutionTreeDiagramEditor editor) {
      return Job.getJobManager().find(editor);
   }
}
