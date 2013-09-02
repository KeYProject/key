/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.keyide.ui.starter;

import org.eclipse.jdt.core.IMethod;
import org.eclipse.ui.IEditorInput;
import org.key_project.key4eclipse.common.ui.starter.IProofStarter;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.editor.input.ProofEditorInput;
import org.key_project.keyide.ui.util.KeYIDEUtil;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * Starts a proof in the KeYIDE user interface integrated in Eclipse.
 * @author Martin Hentschel
 */
public class KeYIDEProofStarter implements IProofStarter {
   /**
    * The unique ID of this starter.
    */
   public static final String STARTER_ID = "org.key_project.keyide.ui.starter.KeYIDEProofStarter";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void open(Proof proof, 
                    KeYEnvironment<CustomConsoleUserInterface> environment, 
                    IMethod method,
                    boolean canStartAutomode,
                    boolean canApplyRules,
                    boolean canPruneProof,
                    boolean canStartSMTSolver) throws Exception {
      IEditorInput input = new ProofEditorInput(proof, environment, method, canStartAutomode, canApplyRules, canPruneProof, canStartSMTSolver);
      WorkbenchUtil.getActivePage().openEditor(input, KeYEditor.EDITOR_ID);
      KeYIDEUtil.switchPerspective();
   }
}