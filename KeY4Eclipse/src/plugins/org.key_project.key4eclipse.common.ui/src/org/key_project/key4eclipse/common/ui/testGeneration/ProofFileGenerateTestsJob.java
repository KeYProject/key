package org.key_project.key4eclipse.common.ui.testGeneration;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.util.eclipse.ResourceUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;

/**
 * A {@link Job} which generates test for a given proof file.
 * @author Martin Hentschel
 */
public class ProofFileGenerateTestsJob extends AbstractGenerateTestsJob {
   /**
    * The {@link IFile} which provides the proof file to generate test cases for.
    */
   private final IFile proofFile;
   
   /**
    * Constructor
    * @param proofFile The {@link IFile} which provides the proof file to generate test cases for.
    */
   public ProofFileGenerateTestsJob(IFile proofFile) {
      super();
      this.proofFile = proofFile;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IStatus run(final IProgressMonitor monitor) {
      KeYEnvironment<DefaultUserInterfaceControl> env = null;
      try {
         env = KeYEnvironment.load(ResourceUtil.getLocation(proofFile), 
                                   KeYResourceProperties.getKeYClassPathEntries(proofFile.getProject()),
                                   KeYResourceProperties.getKeYBootClassPathLocation(proofFile.getProject()));
         generateTests(proofFile.getProject(), 
                       ResourceUtil.getFileNameWithoutExtension(proofFile), 
                       env.getLoadedProof(), 
                       env.getUi(), 
                       monitor);
         return Status.OK_STATUS;
      }
      catch (Exception e) {
         return LogUtil.getLogger().createErrorStatus(e);
      }
      finally {
         if (env != null) {
            env.dispose();
         }
      }
   }
}
