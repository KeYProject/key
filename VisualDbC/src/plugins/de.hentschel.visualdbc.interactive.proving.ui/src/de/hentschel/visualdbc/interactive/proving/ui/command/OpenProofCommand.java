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

package de.hentschel.visualdbc.interactive.proving.ui.command;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.emf.edit.domain.EditingDomain;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeNodeEditPart;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProof2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditor;
import de.hentschel.visualdbc.dbcmodel.presentation.DbcmodelEditor;
import de.hentschel.visualdbc.interactive.proving.ui.job.StartProofJob;

/**
 * Opens the data source user interface to finish the selected {@link DbcProof}.
 * @author Martin Hentschel
 */
public class OpenProofCommand extends AbstractCommand {
   /**
    * {@inheritDoc}
    */
   @Override
   protected void execute(ISelection selection) throws Exception {
      if (selection instanceof IStructuredSelection) {
         Object[] elements = ((IStructuredSelection)selection).toArray();
         if (elements.length >= 1) {
            for (Object element : elements) {
               if (element instanceof DbcProofEditPart) {
                  DbcProofEditPart proofEditPart = (DbcProofEditPart)element;
                  openProof((DbcProof)proofEditPart.getAdapter(DbcProof.class), proofEditPart);
               }
               else if (element instanceof DbcProof2EditPart) {
                  DbcProof2EditPart proofEditPart = (DbcProof2EditPart)element;
                  openProof((DbcProof)proofEditPart.getAdapter(DbcProof.class), proofEditPart);
               }
               else if (element instanceof DbcProof) {
                  openProof((DbcProof)element, null);
               }
               else if (element instanceof IAdaptable) {
                  IAdaptable adaptable = (IAdaptable)element;
                  DbcProof proof = (DbcProof)adaptable.getAdapter(DbcProof.class);
                  if (proof != null) {
                     openProof(proof, null);
                  }
                  else {
                     throw new IllegalArgumentException("Unsupported selection content \"" + element + "");
                  }
               }
               else {
                  throw new IllegalArgumentException("Unsupported selection content \"" + element + "");
               }
            }
         }
         else {
            throw new IllegalArgumentException("No proof selected.");
         }
      }
      else {
         throw new IllegalArgumentException("Unsupported selection \"" + selection + "\".");
      }
   }
   
   /**
    * Returns the {@link EditingDomain} to use.
    * @return The {@link EditingDomain} to use.
    * @throws DSException If it is not possible to get the editing domain.
    */
   protected EditingDomain getEditingDomain() throws DSException {
      // Try to get the domain
      EditingDomain result = null;
      if (getTargetPart() instanceof DbCDiagramEditor) {
         result = ((DbCDiagramEditor)getTargetPart()).getEditingDomain();
      }
      else if (getTargetPart() instanceof DbcmodelEditor) {
         result = ((DbcmodelEditor)getTargetPart()).getEditingDomain();
      }
      else if (getTargetPart() != null) {
         result = (EditingDomain)getTargetPart().getAdapter(EditingDomain.class);
      }
      // Make sure that an editing domain was resolved.
      if (result == null) {
         throw new DSException("Can't get editing domain from workbench part: " + getTargetPart());
      }
      return result;
   }

   /**
    * Opens the proof.
    * @param proof The proof to open
    * @param proofEditPart The {@link DbcProofEditPart} to edit.
    * @throws DSException Occurred Exception
    */
   protected void openProof(DbcProof proof, ShapeNodeEditPart proofEditPart) throws DSException {
      EditingDomain domain = getEditingDomain();
      StartProofJob job = new StartProofJob(domain, proof, proofEditPart);
      job.schedule();
   }
}