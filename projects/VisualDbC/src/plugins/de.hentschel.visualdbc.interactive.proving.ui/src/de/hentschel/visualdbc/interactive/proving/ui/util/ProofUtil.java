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

package de.hentschel.visualdbc.interactive.proving.ui.util;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.emf.common.command.Command;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.edit.command.AddCommand;
import org.eclipse.emf.edit.command.DeleteCommand;
import org.eclipse.emf.edit.command.RemoveCommand;
import org.eclipse.emf.edit.command.SetCommand;
import org.eclipse.emf.edit.domain.EditingDomain;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.Request;
import org.eclipse.gef.RequestConstants;
import org.eclipse.gef.commands.CompoundCommand;
import org.eclipse.gef.internal.GEFMessages;
import org.eclipse.gef.requests.GroupRequest;
import org.eclipse.gmf.runtime.common.core.command.ICommand;
import org.eclipse.gmf.runtime.diagram.ui.commands.DeferredCreateConnectionViewAndElementCommand;
import org.eclipse.gmf.runtime.diagram.ui.commands.ICommandProxy;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ShapeNodeEditPart;
import org.eclipse.gmf.runtime.diagram.ui.requests.CreateConnectionViewAndElementRequest;
import org.eclipse.gmf.runtime.diagram.ui.requests.EditCommandRequestWrapper;
import org.eclipse.gmf.runtime.emf.core.util.EObjectAdapter;
import org.eclipse.gmf.runtime.emf.type.core.IHintedType;
import org.eclipse.gmf.runtime.emf.type.core.requests.SetRequest;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.StringUtil;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSProof;
import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;
import de.hentschel.visualdbc.datasource.model.event.DSProofEvent;
import de.hentschel.visualdbc.datasource.model.event.IDSProofListener;
import de.hentschel.visualdbc.datasource.model.exception.DSCanceledException;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.DbcProofStatus;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;
import de.hentschel.visualdbc.dbcmodel.DbcmodelPackage;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.diagram.custom.util.GMFUtil;
import de.hentschel.visualdbc.dbcmodel.diagram.providers.DbCElementTypes;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDSFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDbcFinder;

/**
 * Provides static methods to work with proofs.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public final class ProofUtil {
   /**
    * Forbid instances.
    */
   private ProofUtil() {
   }
   
   /**
    * Opens the proof and tracks proof status changes and created proof references.
    * @param domain The {@link EditingDomain} to use.
    * @param proof The {@link DbcProof} to open.
    * @param proofEditPart The proof to edit part if available and {@code null} otherwise.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DSException Occurred Exception.
    * @throws DSCanceledException If the progress was canceled.
    */
   public static void openProof(final EditingDomain domain,
                                final DbcProof proof,
                                final ShapeNodeEditPart proofEditPart,
                                IProgressMonitor monitor) throws DSException, DSCanceledException {
      // Make sure that the proof has a target
      if (proof.getTarget() == null) {
         throw new DSException("Proof target not defined.");
      }
      // Get root element with data source settings
      final DbcModel model = DbcModelUtil.getModelRoot(proof);
      if (model != null) {
         // Open connection
         final IDSConnection connection = InteractiveConnectionUtil.openConnection(model, monitor);
         // Get finder
         IDSFinder finder = FinderUtil.getDSFinder(connection);
         if (finder == null) {
            throw new DSException("Can't find finder for connection: " + connection);
         }
         // Get specification
         IDSProvable proveTarget = finder.findProvable(proof.getTarget());
         // Check if obligation is defined
         String obligation = proof.getObligation();
         if (StringUtil.isTrimmedEmpty(obligation)) {
            throw new DSException("No obligation defined.\nValid obligations are:\n -" + CollectionUtil.toString(proveTarget.getObligations(), "\n -"));
         }
         // Check the obligation
         if (!proveTarget.isValidObligation(obligation)) {
            List<String> obligations = proveTarget.getObligations();
            if (CollectionUtil.isEmpty(obligations)) {
               throw new DSException("The obligation \"" + obligation + "\" is invalid.\nNo obligations are available on the proof target.");
            }
            else {
               throw new DSException("The obligation \"" + obligation + "\" is invalid.\nValid obligations are:\n -" + CollectionUtil.toString(obligations, "\n -"));
            }
         }
         // Check if a new proof will be opened and a cleanup is required
         boolean hasInteractiveProof = proveTarget.hasInteractiveProof(obligation);
         if (isProofResetRequired(proof) && !hasInteractiveProof) {
            if (proofEditPart != null) {
               resetProof(proofEditPart, proof);
            }
            else {
               resetProof(domain, proof);
            }
         }
         // Open proof UI
         IDSProof openedDsProof = proveTarget.openInteractiveProof(obligation);
         if (openedDsProof == null) {
            throw new DSException("No proof was opened for \"" + obligation + "\".");
         }
         // Check if the proof was opened the first time
         if (!hasInteractiveProof) {
            // Add listener
            openedDsProof.addProofListener(new IDSProofListener() {
               @Override
               public void proofClosed(DSProofEvent e) {
                  closeProof(domain, proof);
               }

               @Override
               public void referencesChanged(final DSProofEvent e) {
                  updateReferences(domain, connection, model, proof, proofEditPart, e.getNewReferences());
               }
            });
            // Add the initial references to the graph
            synchronized (openedDsProof.getProofReferences()) {
               for (IDSProvableReference provableReference : openedDsProof.getProofReferences()) {
                  // Find target
                  IDbcFinder dbcFinder = FinderUtil.getDbcFinder(connection, model);
                  IDbCProofReferencable target = dbcFinder.findProofReferencable(provableReference.getTargetProvable());
                  String label = provableReference.getLabel();
                  // Make sure that the reference not already exist
                  DbcProofReference existingReference = proof.getProofReference(target, label);
                  if (existingReference == null) {
                     // Create reference
                     if (proofEditPart != null) {
                        createReference(proofEditPart, target, label);
                     }
                     else {
                        createReference(domain, proof, target, label);
                     }
                  }
               }
            }
         }
      }
      else {
         throw new DSException("Can't find model root for: " + proof);
      }
   }

   /**
    * Checks if changes on the proof are required when a new 
    * interactive proof is opened.
    * @param proof The model proof to check.
    * @return {@code true} = required, {@code false} = not required.
    */
   public static boolean isProofResetRequired(DbcProof proof) {
      return InteractiveProvingPreferences.isResetProofIfNewOpened() &&
             (isProofStatusResetRequired(proof) || isProofReferenceResetRequired(proof));
   }
   
   /**
    * Checks if it is required to change the proof status when
    * a new interactive proof is opened.
    * @param proof The model proof to check.
    * @return {@code true} = required, {@code false} = not required.
    */
   public static boolean isProofStatusResetRequired(DbcProof proof) {
      return !DbcProofStatus.OPEN.equals(proof.getStatus());
   }
   
   /**
    * Checks if it is required to clear the proof references when
    * a new interactive proof is opened.
    * @param proof The model proof to check.
    * @return {@code true} = required, {@code false} = not required.
    */
   public static boolean isProofReferenceResetRequired(DbcProof proof) {
      return !proof.getProofReferences().isEmpty();
   }

   /**
    * Resets the proof in diagram and model.
    * @param proofEditPart The proof in diagram to reset.
    * @param proof The proof in model to reset.
    */
   public static void resetProof(ShapeNodeEditPart proofEditPart, DbcProof proof) {
      if (isEditPartAlive(proofEditPart)) {
         CompoundCommand compoundCmd = new CompoundCommand("Proof reset");
         if (isProofReferenceResetRequired(proof)) {
            // Compute the edit parts to delete
            List<Object> editPartsToDelete = new LinkedList<Object>();
            for (DbcProofReference refToDel : proof.getProofReferences()) {
               Collection<EditPart> targetEditPart = GMFUtil.findEditParts(proofEditPart, refToDel);
               editPartsToDelete.addAll(targetEditPart);
            }
            // Create delete reference commands
            // See: org.eclipse.gef.ui.actions.DeleteAction#createDeleteCommand(java.util.List)
            GroupRequest deleteReq = new GroupRequest(RequestConstants.REQ_DELETE);
            deleteReq.setEditParts(editPartsToDelete);
            for (int i = 0; i < editPartsToDelete.size(); i++) {
               EditPart object = (EditPart) editPartsToDelete.get(i);
               org.eclipse.gef.commands.Command cmd = object.getCommand(deleteReq);
               if (cmd != null) {
                  compoundCmd.add(cmd);
               }
            }
         }
         if (isProofResetRequired(proof)) {
            // Add set status command
            Request request = new EditCommandRequestWrapper(new SetRequest(proof, DbcmodelPackage.Literals.DBC_PROOF__STATUS, DbcProofStatus.OPEN));
            org.eclipse.gef.commands.Command setCmd = proofEditPart.getCommand(request); 
            compoundCmd.add(setCmd);
         }
         // Execute delete command
         proofEditPart.getDiagramEditDomain().getDiagramCommandStack().execute(compoundCmd);
      }
   }
   
   /**
    * Resets the proof in model only.
    * @param domain The {@link EditingDomain} to use.
    * @param proof The proof to reset.
    */
   public static void resetProof(EditingDomain domain, DbcProof proof) {
      if (isEditingDomainAlive(domain)) {
         org.eclipse.emf.common.command.CompoundCommand cmd = new org.eclipse.emf.common.command.CompoundCommand("Proof reset");
         if (isProofStatusResetRequired(proof)) {
            Command setStatusCmd = SetCommand.create(domain, proof, DbcmodelPackage.Literals.DBC_PROOF__STATUS, DbcProofStatus.OPEN);
            cmd.append(setStatusCmd);
         }
         if (isProofReferenceResetRequired(proof)) {
            Command delReferencesCmd = DeleteCommand.create(domain, proof.getProofReferences());
            cmd.append(delReferencesCmd);
         }
         domain.getCommandStack().execute(cmd);
      }
   }

   /**
    * Closes the {@link DbcProof}.
    * @param domain The {@link EditingDomain} to use.
    * @param proof The {@link DbcProof} to close.
    */
   public static void closeProof(EditingDomain domain, DbcProof proof) {
      // Check if status change is possible and required
      if (proof != null && !DbcProofStatus.FULFILLED.equals(proof.getStatus()) && isEditingDomainAlive(domain)) {
         // Change status to fulfilled
         Command cmd = SetCommand.create(domain, proof, DbcmodelPackage.Literals.DBC_PROOF__STATUS, DbcProofStatus.FULFILLED);
         domain.getCommandStack().execute(cmd);
      }
   }

   /**
    * Makes sure that the given {@link EditingDomain} is still alive.
    * @param domain The {@link EditingDomain} to check.
    * @return {@code true} is alive, {@code false} is disposed.
    */
   protected static boolean isEditingDomainAlive(EditingDomain domain) {
      return domain != null && domain.getCommandStack() != null;
   }

   /**
    * Makes sure that the given {@link ShapeNodeEditPart} is still alive.
    * @param editPart The {@link ShapeNodeEditPart} to check.
    * @return {@code true} is alive, {@code false} is disposed.
    */
   protected static boolean isEditPartAlive(ShapeNodeEditPart editPart) {
      return editPart != null && isEditingDomainAlive(editPart.getEditingDomain());
   }

   /**
    * Creates a new proof references in the domain model and removes
    * old ones if required.
    * @param domain The {@link EditingDomain} to use.
    * @param connection The {@link IDSConnection} to use.
    * @param model The {@link DbcModel} to use.
    * @param proof The {@link DbcProof} to close.
    * @param proofEditPart The proof to edit part if available and {@code null} otherwise.
    * @param references The now available references.
    */
   public static void updateReferences(final EditingDomain domain, 
                                       IDSConnection connection,
                                       DbcModel model,
                                       DbcProof proof, 
                                       ShapeNodeEditPart proofEditPart,
                                       List<IDSProvableReference> references) {
      try {
         // Get finder to search dbc elements
         IDbcFinder finder = FinderUtil.getDbcFinder(connection, model);
         if (finder == null) {
            throw new DSException("Can't find finder for connection: " + connection);
         }
         // Add all new references to the DbC model and compute which references are no longer needed
         List<DbcProofReference> referencesToDelete = new LinkedList<DbcProofReference>(proof.getProofReferences());
         for (IDSProvableReference provableReference : references) {
            // Find target
            IDbCProofReferencable target = finder.findProofReferencable(provableReference.getTargetProvable());
            String label = provableReference.getLabel();
            // Make sure that the reference not already exist
            DbcProofReference existingReference = proof.getProofReference(target, label);
            if (existingReference == null) {
               // Create reference
               if (proofEditPart != null) {
                  createReference(proofEditPart, target, label);
               }
               else {
                  createReference(domain, proof, target, label);
               }
            }
            else {
               referencesToDelete.remove(existingReference); // Keep existing reference, so remove it from the delete list
            }
         }
         if (!referencesToDelete.isEmpty()) {
            if (proofEditPart != null) {
               deleteReferences(proofEditPart, referencesToDelete);
            }
            else {
               deleteReferences(domain, proof, referencesToDelete);
            }
         }
      }
      catch (DSException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(null, e);
      }
   }
   
   /**
    * Deletes the references in the domain and diagram model.
    * @param proofEditPart The proof to edit.
    * @param referencesToDelete The references to delete.
    */
   public static void deleteReferences(ShapeNodeEditPart proofEditPart, List<DbcProofReference> referencesToDelete) {
      if (isEditPartAlive(proofEditPart)) {
         // Compute the edit parts to delete
         List<Object> editPartsToDelete = new LinkedList<Object>();
         for (DbcProofReference refToDel : referencesToDelete) {
            Collection<EditPart> targetEditPart = GMFUtil.findEditParts(proofEditPart, refToDel);
            editPartsToDelete.addAll(targetEditPart);
         }
         // Create delete reference commands
         // See: org.eclipse.gef.ui.actions.DeleteAction#createDeleteCommand(java.util.List)
         GroupRequest deleteReq = new GroupRequest(RequestConstants.REQ_DELETE);
         deleteReq.setEditParts(editPartsToDelete);
         CompoundCommand compoundCmd = new CompoundCommand(GEFMessages.DeleteAction_ActionDeleteCommandName);
         for (int i = 0; i < editPartsToDelete.size(); i++) {
            EditPart object = (EditPart) editPartsToDelete.get(i);
            org.eclipse.gef.commands.Command cmd = object.getCommand(deleteReq);
            if (cmd != null) {
               compoundCmd.add(cmd);
            }
         }
         // Execute delete command
         proofEditPart.getDiagramEditDomain().getDiagramCommandStack().execute(compoundCmd);
      }
   }

   /**
    * Deletes the given proof references in the domain model only.
    * @param domain  The {@link EditingDomain} to use.
    * @param proof The proof to modify.
    * @param referencesToDelete The references to delete.
    */
   public static void deleteReferences(EditingDomain domain, DbcProof proof, List<DbcProofReference> referencesToDelete) {
      if (isEditingDomainAlive(domain)) {
         Command removeCmd = RemoveCommand.create(domain, proof, DbcmodelPackage.Literals.DBC_PROOF__PROOF_REFERENCES, referencesToDelete);
         domain.getCommandStack().execute(removeCmd);
      }
   }

   /**
    * Creates a proof reference directly in the domain model.
    * @param domain The {@link EditingDomain} to use.
    * @param proof The proof reference source.
    * @param target The proof reference target.
    * @param label The proof reference label.
    */
   public static void createReference(EditingDomain domain,
                                      DbcProof proof,
                                      IDbCProofReferencable target,
                                      String label){
      if (isEditingDomainAlive(domain)) {
         DbcProofReference newReference = DbcmodelFactory.eINSTANCE.createDbcProofReference();
         newReference.setKind(label);
         newReference.setTarget(target);
         Command cmd = AddCommand.create(domain, proof, DbcmodelPackage.Literals.DBC_PROOF__PROOF_REFERENCES, newReference);
         domain.getCommandStack().execute(cmd);
      }
   }
   
   /**
    * Creates a proof reference in the diagram and model.
    * @param proofEditPart The proof reference source edit part.
    * @param target The proof reference target.
    * @param label The proof reference label.
    */
   public static void createReference(ShapeNodeEditPart proofEditPart,
                                      IDbCProofReferencable target,
                                      String label) {
      if (isEditPartAlive(proofEditPart)) {
         // Find target edit part
         EditPart targetEditPart = proofEditPart.findEditPart(proofEditPart.getRoot(), target);
         // Create create reference request
         CreateConnectionViewAndElementRequest viewAndElementRequest = new CreateConnectionViewAndElementRequest(
               DbCElementTypes.DbcProofReference_4002,
               ((IHintedType)DbCElementTypes.DbcProofReference_4002).getSemanticHint(), 
               proofEditPart.getDiagramPreferencesHint());
         Map<Object, Object> extendedData = new HashMap<Object, Object>();
         extendedData.put(DbcmodelPackage.Literals.DBC_PROOF_REFERENCE__KIND, label);
         viewAndElementRequest.setExtendedData(extendedData); // This information is handled in DbcProofReferenceCreateCommand
         // Create create reference command
         ICommand createReferenceCmd = new DeferredCreateConnectionViewAndElementCommand(
               viewAndElementRequest,
               new EObjectAdapter((EObject) proofEditPart.getModel()),
               targetEditPart, 
               proofEditPart.getViewer());
         ICommandProxy createReferenceProxy = new ICommandProxy(createReferenceCmd);
         CompoundCommand cc = new CompoundCommand("Create Proof Reference");
         cc.add(createReferenceProxy);
         // Execute create reference command
         proofEditPart.getDiagramEditDomain().getDiagramCommandStack().execute(cc);
      }
   }
}