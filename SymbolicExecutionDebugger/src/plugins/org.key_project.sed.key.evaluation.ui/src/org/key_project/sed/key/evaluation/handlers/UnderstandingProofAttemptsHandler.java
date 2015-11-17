package org.key_project.sed.key.evaluation.handlers;

import java.io.File;
import java.io.FileOutputStream;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.sed.key.evaluation.Activator;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputReader;
import org.key_project.sed.key.evaluation.model.io.EvaluationInputWriter;
import org.key_project.sed.key.evaluation.util.LogUtil;
import org.key_project.sed.key.evaluation.util.SEDEvaluationImages;
import org.key_project.sed.key.evaluation.wizard.EvaluationWizard;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.IOUtil;

/**
 * Handler to open the {@link EvaluationWizard} 
 * performing the {@link UnderstandingProofAttemptsEvaluation}.
 * @author Martin Hentschel
 */
public class UnderstandingProofAttemptsHandler extends AbstractHandler {
   public static final File STATE_LOCATION_FILE;
   
   /**
    * The {@link EvaluationInput} to perform {@link #INSTANCE}.
    */
   public static EvaluationInput INPUT_INSTANCE;
   
   /**
    * Static constructor.
    */
   static {
      String statePath = Activator.getDefault().getStateLocation().toString();
      STATE_LOCATION_FILE = new File(statePath, "UnderstandingProofAttempts.xml");
      try {
         if (!STATE_LOCATION_FILE.isFile()) {
            throw new IllegalStateException("File " + STATE_LOCATION_FILE + " does not exist.");
         }
         else {
            EvaluationInput readInput = EvaluationInputReader.parse(STATE_LOCATION_FILE);
            if (readInput.getEvaluation() instanceof UnderstandingProofAttemptsEvaluation) {
               INPUT_INSTANCE = readInput;
            }
            else {
               throw new IllegalStateException("Wrong evaluation read."); 
            }
         }
      }
      catch (Exception e) {
         INPUT_INSTANCE = new EvaluationInput(UnderstandingProofAttemptsEvaluation.INSTANCE);
      }
   }
   
   /**
    * {@inheritDoc}
    */
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
	   // Close welcome view
	   WorkbenchUtil.closeWelcomeView();
      // Open wizard
	   EvaluationWizard.openWizard(HandlerUtil.getActiveShell(event), true, INPUT_INSTANCE, SEDEvaluationImages.getImageDescriptor(SEDEvaluationImages.EVALUATION_WIZARD_KEY), SEDEvaluationImages.getImage(SEDEvaluationImages.EVALUATION_KEY));
//	   new EvaluationWizardDialog(HandlerUtil.getActiveShell(event), true, BrowserExampleEvaluation.INSTANCE_INPUT).open();
		return null;
	}

	/**
	 * Saves {@link #INPUT_INSTANCE} in the state location.
	 */
	public static void saveEvaluationInput() {
	   try {
         String xml = EvaluationInputWriter.toXML(INPUT_INSTANCE);
         IOUtil.writeTo(new FileOutputStream(STATE_LOCATION_FILE), xml, IOUtil.DEFAULT_CHARSET);
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
      }
	}
}
