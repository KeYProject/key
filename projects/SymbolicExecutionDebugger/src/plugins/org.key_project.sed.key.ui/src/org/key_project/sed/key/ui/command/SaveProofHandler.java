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

package org.key_project.sed.key.ui.command;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.dialogs.SaveAsDialog;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.ui.util.LogUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;

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
                  IMethod method = keyTarget.getMethod();
                  // Open save dialog
                  SaveAsDialog dialog = new SaveAsDialog(HandlerUtil.getActiveShell(event));
                  String proofFileName = target.getName() + "." + KeYUtil.PROOF_FILE_EXTENSION;
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
                     IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(path);
                     File location = ResourceUtil.getLocation(file);
                     // Create proof file content
                     ProofSaver saver = new ProofSaver(proof, location.getAbsolutePath(), Main.INTERNAL_VERSION);
                     ByteArrayOutputStream out = new ByteArrayOutputStream();
                     String errorMessage = saver.save(out);
                     if (errorMessage != null) {
                        throw new CoreException(LogUtil.getLogger().createErrorStatus(errorMessage));
                     }
                     // Save proof file content
                     if (file.exists()) {
                        file.setContents(new ByteArrayInputStream(out.toByteArray()), true, true, null);
                     }
                     else {
                        file.create(new ByteArrayInputStream(out.toByteArray()), true, null);
                     }
                  }
               }
            }
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(HandlerUtil.getActiveShell(event), e);
      }
      return null;
   }
}