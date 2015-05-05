package org.key_project.sed.key.evaluation.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.sed.key.evaluation.model.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.wizard.EvaluationWizard;

/**
 * Handler to open the {@link EvaluationWizard} 
 * performing the {@link UnderstandingProofAttemptsEvaluation}.
 * @author Martin Hentschel
 */
public class UnderstandingProofAttemptsHandler extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
	   EvaluationWizard.openWizard(HandlerUtil.getActiveShell(event), UnderstandingProofAttemptsEvaluation.INPUT_INSTANCE);
		return null;
	}
}
