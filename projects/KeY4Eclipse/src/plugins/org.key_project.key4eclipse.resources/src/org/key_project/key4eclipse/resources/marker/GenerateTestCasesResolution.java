package org.key_project.key4eclipse.resources.marker;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.graphics.Image;
import org.key_project.key4eclipse.common.ui.testGeneration.ProofFileGenerateTestsJob;
import org.key_project.key4eclipse.common.ui.util.KeYImages;

/**
 * Provides the QuickFixes for the KeY{@link IMarker} which generate test cases.
 * @author Stefan Käsdorf
 */
public class GenerateTestCasesResolution extends AbstractProofMarkerResolution {
   /**
    * Initializes the global variables depending on the given {@link IMarker#getType()}.
    * @param marker - the given {@link IMarker}
    * @throws CoreException 
    */
   public GenerateTestCasesResolution(IMarker marker) throws CoreException {
      super(marker);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getClosedMarkerDescriptionPrefix() {
      return "Generate test cases for proof: ";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getNotClosedMarkerDescriptionPrefix() {
      return "Generate executable JUnit test cases.";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getLabelPrefix() {
      return "Generate test cases: ";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage() {
      return KeYImages.getImage(KeYImages.TEST_GENERATION);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void run(IMarker marker, IFile proofFile) throws Exception {
      new ProofFileGenerateTestsJob(proofFile).schedule();
   }
}
