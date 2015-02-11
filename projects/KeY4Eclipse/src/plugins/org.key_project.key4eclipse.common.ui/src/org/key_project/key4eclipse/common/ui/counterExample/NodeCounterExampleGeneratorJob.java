package org.key_project.key4eclipse.common.ui.counterExample;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.key_project.key4eclipse.common.ui.util.LogUtil;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Node;

/**
 * A {@link Job} which generates counter examples for a given {@link Node}.
 * @author Martin Hentschel
 */
public class NodeCounterExampleGeneratorJob extends Job {
   /**
    * The {@link KeYMediator} to use.
    */
   private final KeYMediator mediator;
   
   /**
    * The {@link Node} to find a counterexample for.
    */
   private final Node node;
   
   /**
    * Constructor.
    * @param mediator The {@link KeYMediator} to use.
    * @param node The {@link Node} to find a counterexample for.
    */
   public NodeCounterExampleGeneratorJob(KeYMediator mediator, Node node) {
      super("Generating counterexamples");
      this.mediator = mediator;
      this.node = node;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IStatus run(IProgressMonitor monitor) {
      try {
         new EclipseCounterExampleGenerator().searchCounterExample(mediator, node.proof(), node.sequent());
         return Status.OK_STATUS;
      }
      catch (Exception e) {
         return LogUtil.getLogger().createErrorStatus(e);
      }
   }
}
