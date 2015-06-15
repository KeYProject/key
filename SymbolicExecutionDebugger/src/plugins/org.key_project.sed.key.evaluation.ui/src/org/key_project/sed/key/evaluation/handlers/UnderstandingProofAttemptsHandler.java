package org.key_project.sed.key.evaluation.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.wizard.EvaluationWizard;

/**
 * Handler to open the {@link EvaluationWizard} 
 * performing the {@link UnderstandingProofAttemptsEvaluation}.
 * @author Martin Hentschel
 */
public class UnderstandingProofAttemptsHandler extends AbstractHandler {
   /**
    * The {@link EvaluationInput} to perform {@link #INSTANCE}.
    */
   public static EvaluationInput INPUT_INSTANCE = new EvaluationInput(UnderstandingProofAttemptsEvaluation.INSTANCE);
   
   /**
    * {@inheritDoc}
    */
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
	   EvaluationWizard.openWizard(HandlerUtil.getActiveShell(event), true, INPUT_INSTANCE);
		return null;
	}
}
