package org.key_project.sed.ui.visualization.execution_tree.editor;

import org.eclipse.core.runtime.jobs.Job;
import org.key_project.util.eclipse.job.ObjectchedulingRule;

/**
 * Abstract super class for {@link Job}s executed in an {@link ExecutionTreeDiagramEditor}
 * which have to be executed in serial order. 
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionTreeDiagramEditorJob extends Job {
   /**
    * Constructor.
    * @param name The name of this {@link Job}.
    * @param editor The {@link ExecutionTreeDiagramEditor} which has executed this {@link Job}.
    */
   public AbstractExecutionTreeDiagramEditorJob(String name, ExecutionTreeDiagramEditor editor) {
      super(name);
      setRule(new ObjectchedulingRule(editor));
   }
}
