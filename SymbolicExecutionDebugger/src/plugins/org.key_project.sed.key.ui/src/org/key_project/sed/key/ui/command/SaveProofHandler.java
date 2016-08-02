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

package org.key_project.sed.key.ui.command;

import java.io.IOException;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IContainer;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.dialogs.SaveAsDialog;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.ui.util.LogUtil;
import org.key_project.sed.key.ui.view.ProofView;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.util.KeYConstants;
import de.uka.ilkd.key.util.MiscTools;

/**
 * This {@link IHandler} opens a save as dialog to save the {@link Proof}
 * of the currently selected {@link KeYDebugTarget}s as *.proof file.
 * @author Martin Hentschel
 */
public class SaveProofHandler extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      try {
         IWorkbenchPart part = HandlerUtil.getActivePart(event);
         if (part instanceof ProofView) {
            saveProofViewProof((ProofView) part, event);
         }
         else {
            saveDebugSelection(event);
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(HandlerUtil.getActiveShell(event), e);
      }
      return null;
   }
   
   /**
    * Saves the {@link Proof} of the given {@link ProofView}.
    * @param proofView The {@link ProofView}.
    * @param event The current {@link ExecutionEvent} to work with.
    * @throws CoreException Occurred Exception.
    */
   protected void saveProofViewProof(ProofView proofView, ExecutionEvent event) throws CoreException {
      KeYDebugTarget target = proofView.getKeyDebugTarget();
      if (target != null) {
         saveProof(target, proofView.getCurrentProof(), HandlerUtil.getActiveShell(event));
      }
   }

   /**
    * Saves the current debug view selection.
    * @param event The {@link ExecutionEvent} to work with.
    * @throws CoreException Occurred Exception.
    */
   protected void saveDebugSelection(ExecutionEvent event) throws CoreException {
      ISelection selection = HandlerUtil.getCurrentSelection(event);
      Object[] elements = SWTUtil.toArray(selection);
      for (Object element : elements) {
         // Find proof
         if (element instanceof ILaunch) {
            element = ((ILaunch)element).getDebugTarget();
         }
         if (element instanceof IDebugElement) {
            IDebugTarget target = ((IDebugElement)element).getDebugTarget();
            if (target instanceof KeYDebugTarget) {
               KeYDebugTarget keyTarget = (KeYDebugTarget)target;
               Proof proof = keyTarget.getProof();
               saveProof(keyTarget, proof, HandlerUtil.getActiveShell(event));
            }
         }
      }
   }
   
   /**
    * Saves the given {@link Proof} of the given {@link KeYDebugTarget}.
    * @param keyTarget The {@link KeYDebugTarget} to save.
    * @param proof The {@link Proof} to save.
    * @param shell The parent {@link Shell}.
    * @throws CoreException Occurred Exception.
    */
   protected void saveProof(KeYDebugTarget keyTarget, Proof proof, Shell shell) throws CoreException {
      if (proof.getProofFile() != null) { // Check if proof file already exists
         ProofSaver saver = new ProofSaver(proof, proof.getProofFile().getAbsolutePath(), KeYConstants.INTERNAL_VERSION);
         String errorMsg;
         try {
             errorMsg = saver.save();
         }
         catch (IOException e) {
             errorMsg = e.toString();
         }
         if (errorMsg != null) {
            saveAs(keyTarget, shell);
         }
      }
      else {
         saveAs(keyTarget, shell);
      }
   }

   /**
    * Open the save as dialog.
    * @param target The {@link KeYDebugTarget} to save.
    * @param shell The parent {@link Shell}.
    * @throws CoreException Occurred Exception.
    */
   public void saveAs(KeYDebugTarget target, Shell shell) throws CoreException {
      IMethod method = target.getMethod();
      // Open save dialog
      SaveAsDialog dialog = new SaveAsDialog(shell);
      String proofFileName = MiscTools.toValidFileName(target.getName()) + "." + KeYUtil.PROOF_FILE_EXTENSION;
      if (method != null && method.getResource() != null) {
         IContainer parent = method.getResource().getParent();
         dialog.setOriginalFile(parent.getFile(new Path(proofFileName)));
      }
      else {
         dialog.setOriginalName(proofFileName);
      }
      dialog.create();
      dialog.setTitle("Save Symbolic Execution Tree as Proof File");
      dialog.setMessage("Save KeY's proof from which the symbolic execution tree was extracted as *.proof file.");
      if (dialog.open() == SaveAsDialog.OK) {
         IPath path = dialog.getResult();
         KeYUtil.saveProof(target.getProof(), path);
      }
   }
}