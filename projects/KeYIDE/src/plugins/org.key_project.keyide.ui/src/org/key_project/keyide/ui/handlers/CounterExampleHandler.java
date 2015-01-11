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

package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.counterExample.NodeCounterExampleGeneratorJob;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.counterexample.AbstractCounterExampleGenerator;

/**
 * This {@link IHandler} searches for a counterexample.
 * @author Martin Hentschel
 */
public class CounterExampleHandler extends AbstractSaveExecutionHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      if (AbstractCounterExampleGenerator.isSolverAvailable()) {
         IEditorPart editorPart = HandlerUtil.getActiveEditor(event);
         if (editorPart instanceof KeYEditor) {
            KeYEditor editor = (KeYEditor) editorPart;
            ISelection selection = HandlerUtil.getCurrentSelection(event);
            Object[] elements = SWTUtil.toArray(selection);
            for (Object element : elements) {
                if (element instanceof Node) {
                    Job job = new NodeCounterExampleGeneratorJob(editor.getMediator(), (Node) element);
                    job.schedule();
                }
            }
         }
      }
      else {
         MessageDialog.openError(HandlerUtil.getActiveShell(event), "Error", "SMT Solver '" + SolverType.Z3_CE_SOLVER + "' is not available.\nPlease configure the SMT Solver Options in the main window of KeY.");
      }
      return null;
   }
}