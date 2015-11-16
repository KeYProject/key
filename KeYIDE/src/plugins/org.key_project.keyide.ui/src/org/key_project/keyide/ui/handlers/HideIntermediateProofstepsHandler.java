/**
 * 
 */
package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.handlers.HandlerUtil;

/**
 * toggles the state for hiding intermediate proofsteps
 * 
 * @author Seena Vellaramkalayil, Leonard Goetz
 */
public class HideIntermediateProofstepsHandler extends AbstractHandler {

	/**
	 * command id
	 */
	public static final String COMMAND_ID = "org.key_project.keyide.ui.commands.hideIntermediateProofsteps";

	/** 
	 * {@inheritDoc}
	 */
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		HandlerUtil.toggleCommandState(event.getCommand());
		return null;
	}
}
