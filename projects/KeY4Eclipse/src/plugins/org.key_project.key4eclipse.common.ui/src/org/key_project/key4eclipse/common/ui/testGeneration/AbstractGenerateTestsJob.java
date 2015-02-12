package org.key_project.key4eclipse.common.ui.testGeneration;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.jobs.Job;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.testgen.MemoryTestGenerationLog;
import de.uka.ilkd.key.smt.testgen.StopRequest;

/**
 * A {@link Job} which provides the basic functionality to generate test cases.
 * @author Martin Hentschel
 */
public abstract class AbstractGenerateTestsJob extends Job {
   /**
    * Constructor.
    */
   public AbstractGenerateTestsJob() {
      super("Generate Test Cases");
   }

   /**
    * Performs the test case generation.
    * @param sourceProject The {@link IProject} which provides the source code.
    * @param testFileName The name of the test file to generate.
    * @param proof The {@link Proof} to generate test cases for.
    * @param mediator The {@link KeYMediator} to use.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws Exception Occurred Exception.
    */
   protected void generateTests(final IProject sourceProject, 
                                final String testFileName, 
                                final Proof proof, 
                                final KeYMediator mediator, 
                                final IProgressMonitor monitor) throws Exception {
      EclipseTestGenerator testGenerator = null;
      try {
         MemoryTestGenerationLog log = new MemoryTestGenerationLog();
         testGenerator = new EclipseTestGenerator(sourceProject, 
                                                  testFileName, 
                                                  mediator, 
                                                  proof);
         testGenerator.generateTestCases(new StopRequest() {
            @Override
            public boolean shouldStop() {
               return monitor.isCanceled();
            }
         }, log);
      }
      finally {
         if (testGenerator != null) {
            testGenerator.dispose();
         }
      }
   }
}
