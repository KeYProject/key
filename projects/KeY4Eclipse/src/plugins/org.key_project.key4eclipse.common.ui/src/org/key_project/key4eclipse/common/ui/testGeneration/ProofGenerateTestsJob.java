package org.key_project.key4eclipse.common.ui.testGeneration;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.key_project.key4eclipse.common.ui.util.LogUtil;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;

/**
 * A {@link Job} which generates test for a given proof file.
 * @author Martin Hentschel
 */
public class ProofGenerateTestsJob extends AbstractGenerateTestsJob {
   /**
    * The {@link IProject} which provides the source code.
    */
   private final IProject sourceProject;
   
   /**
    * The {@link Proof} to generate test cases for.
    */
   private final Proof proof;
   
   /**
    * The {@link UserInterfaceControl} to use.
    */
   private final UserInterfaceControl ui;
   
   /**
    * Constructor.
    * @param sourceProject The {@link IProject} which provides the source code.
    * @param proof The {@link Proof} to generate test cases for.
    * @param ui The {@link UserInterfaceControl} to use.
    */
   public ProofGenerateTestsJob(IProject sourceProject, Proof proof, UserInterfaceControl ui) {
      super();
      this.sourceProject = sourceProject;
      this.proof = proof;
      this.ui = ui;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IStatus run(final IProgressMonitor monitor) {
      try {
         generateTests(sourceProject, 
                       proof.name().toString(), 
                       proof, 
                       ui, 
                       monitor);
         return Status.OK_STATUS;
      }
      catch (Exception e) {
         return LogUtil.getLogger().createErrorStatus(e);
      }
   }
}
