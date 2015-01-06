package org.key_project.key4eclipse.common.ui.testGeneration;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.util.eclipse.ResourceUtil;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.testgen.MemoryTestGenerationLog;
import de.uka.ilkd.key.smt.testgen.StopRequest;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * A {@link Job} which generates test for a given proof file.
 * @author Martin Hentschel
 */
public class GenerateTestsJob extends Job {
   /**
    * The {@link IFile} which provides the proof file to generate test cases for.
    */
   private final IFile proofFile;
   
   /**
    * Constructor
    * @param proofFile The {@link IFile} which provides the proof file to generate test cases for.
    */
   public GenerateTestsJob(IFile proofFile) {
      super("Generate Test Cases");
      this.proofFile = proofFile;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IStatus run(final IProgressMonitor monitor) {
      KeYEnvironment<CustomUserInterface> env = null;
      EclipseTestGenerator testGenerator = null;
      try {
         env = KeYEnvironment.load(ResourceUtil.getLocation(proofFile), 
                                   KeYResourceProperties.getKeYClassPathEntries(proofFile.getProject()),
                                   KeYResourceProperties.getKeYBootClassPathLocation(proofFile.getProject()));
         Proof proof = env.getLoadedProof();
         
         MemoryTestGenerationLog log = new MemoryTestGenerationLog();
         testGenerator = new EclipseTestGenerator(proofFile, env.getMediator(), proof);
         testGenerator.generateTestCases(new StopRequest() {
            @Override
            public boolean shouldStop() {
               return monitor.isCanceled();
            }
         }, log);
         return Status.OK_STATUS;
      }
      catch (Exception e) {
         return LogUtil.getLogger().createErrorStatus(e);
      }
      finally {
         if (testGenerator != null) {
            testGenerator.dispose();
         }
         if (env != null) {
            env.dispose();
         }
      }
   }
}
