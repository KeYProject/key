/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package de.hentschel.visualdbc.dbcmodel.diagram.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.handlers.RadioState;

/**
 * <p>
 * Handler which is executed to change the shown and hidden proof references.
 * </p>
 * <p>
 * During execution only the command state is changed. The diagram editors
 * itself registers the change and updates the shown content.
 * </p>
 * @author Martin Hentschel
 * @generated NOT
 */
public class AutomaticProofReferenceHidingHandler extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      if (!HandlerUtil.matchesRadioState(event)) {
         String currentState = event.getParameter(RadioState.PARAMETER_ID);      
         HandlerUtil.updateRadioState(event.getCommand(), currentState);
      }
      return null;
   }
}