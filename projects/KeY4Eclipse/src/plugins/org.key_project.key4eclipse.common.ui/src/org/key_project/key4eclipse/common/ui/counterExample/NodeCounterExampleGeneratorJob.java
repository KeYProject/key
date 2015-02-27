package org.key_project.key4eclipse.common.ui.counterExample;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.key_project.key4eclipse.common.ui.util.LogUtil;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.ui.UserInterface;

/**
 * A {@link Job} which generates counter examples for a given {@link Node}.
 * @author Martin Hentschel
 */
public class NodeCounterExampleGeneratorJob extends Job {
   /**
    * The {@link UserInterface} to use.
    */
   private final UserInterface ui;
   
   /**
    * The {@link Node} to find a counterexample for.
    */
   private final Node node;
   
   /**
    * Constructor.
    * @param ui The {@link UserInterface} to use.
    * @param node The {@link Node} to find a counterexample for.
    */
   public NodeCounterExampleGeneratorJob(UserInterface ui, Node node) {
      super("Generating counterexamples");
      this.ui = ui;
      this.node = node;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IStatus run(IProgressMonitor monitor) {
      try {
         new EclipseCounterExampleGenerator().searchCounterExample(ui, node.proof(), node.sequent());
         return Status.OK_STATUS;
      }
      catch (Exception e) {
         return LogUtil.getLogger().createErrorStatus(e);
      }
   }
}
