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

package de.hentschel.visualdbc.dbcmodel.diagram.custom.action;

import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.gef.EditPart;
import org.eclipse.gmf.runtime.diagram.ui.parts.DiagramEditor;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
import de.hentschel.visualdbc.dbcmodel.diagram.custom.util.GMFUtil;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCAxiomContractEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCAxiomContractEditPart.DbcAxiomContractFigure;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAttributeEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAttributeEditPart.DbcAttributeFigure;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcAxiomEditPart.DbcAxiomFigure;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClass2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcClass2EditPart.DbcClassFigure;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorEditPart.DbcConstructorFigure;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnum2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnum2EditPart.DbcEnumFigure;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumLiteralEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcEnumLiteralEditPart.DbcEnumLiteralFigure;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterface2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInterface2EditPart.DbcInterfaceFigure;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInvariantEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInvariantEditPart.DbcInvariantFigure;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcMethodEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcMethodEditPart.DbcMethodFigure;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcOperationContractEditPart.DbcOperationContractFigure;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProof2EditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProof2EditPart.DbcProofFigure;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofReferenceEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofReferenceEditPart.DbcProofReferenceFigure;

/**
 * <p>
 * This {@link IEditorActionDelegate} contains the whole functionality
 * to highlight elements based on the current selection in context
 * of proof references. This means that for selected proof references source
 * and target is also highlighted; for proofs all references and their
 * targets are selected and for proof referenceable elements that all
 * incoming references and their source proofs are selected.
 * </p>
 * <p>
 * The highlighting functionality is enabled or disabled based on the
 * selection of the {@link IAction} which manages this {@link IEditorActionDelegate}.
 * </p>
 * @author Martin Hentschel
 */
public class AutomaticProofReferenceHighlightEditorActionDelegate implements IEditorActionDelegate {
   /**
    * The {@link Color} which is used for highlighting.
    */
   public static final Color HIGHLIGHT_COLOR = new Color(Display.getDefault(), 52, 80, 116);
   
   /**
    * The line width used for highlighting.
    */
   public static final int HIGHLIGHT_LINE_WIDTH = 3;
   
   /**
    * The target {@link IEditorPart}.
    */
   private IEditorPart targetEditor;

   /**
    * The current selection in {@link #targetEditor}.
    */
   private ISelection selection;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void run(IAction action) {
      updateHighlighting(action);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void selectionChanged(IAction action, ISelection selection) {
      this.selection = selection;
      updateHighlighting(action);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setActiveEditor(final IAction action, IEditorPart targetEditor) {
      this.targetEditor = targetEditor;
      this.selection = null;
      updateHighlighting(action);
   }

   /**
    * Highlights elements based on the selected elements in context
    * of proof references.
    * @param action The {@link IAction} which enables/disables the automatic highlighting.
    */
   protected void updateHighlighting(IAction action) {
      if (targetEditor instanceof DiagramEditor) {
         DiagramEditor editor = (DiagramEditor)targetEditor;
         List<?> selectedElements = SWTUtil.toList(selection);
         List<?> selectedModelElements = GMFUtil.getModelObjects(selectedElements);
         Map<?, ?> map = editor.getDiagramGraphicalViewer().getEditPartRegistry();
         // Iterate over all EditParts of the diagram
         for (Object obj : map.values()) {
            if (obj instanceof EditPart) {
               // Compute highlight state
               Object modelObject = GMFUtil.getModelObject((EditPart)obj);
               Boolean highlight = shouldHighlight(modelObject, action, selectedModelElements);
               // Check if highlighting is required
               if (highlight != null) {
                  changeHighlightState(obj, highlight);
               }
            }
         }
      }
   }

   /**
    * Computes if the given model {@link Object} should be highlighted
    * in diagram representation or not.
    * @param modelObject The model {@link Object} to check.
    * @param action The {@link IAction} which defines the global highlighting enabled state.
    * @param selectedModelElements The currently selected model elements.
    * @return {@code Boolean#TRUE} = highlight, {@code Boolean#FALSE} = do not highlight, {@code null} never highlight.
    */
   protected Boolean shouldHighlight(Object modelObject, IAction action, List<?> selectedModelElements) {
      Boolean highlight = null;
      if (modelObject instanceof IDbCProofReferencable) {
         if (action.isChecked()) {
            IDbCProofReferencable referencable = (IDbCProofReferencable)modelObject;
            Iterator<DbcProofReference> iter = referencable.getAllReferences().iterator();
            highlight = selectedModelElements.contains(modelObject);
            while (!highlight && iter.hasNext()) {
               DbcProofReference next = iter.next();
               if (selectedModelElements.contains(next) ||
                   selectedModelElements.contains(next.getSource())) {
                  highlight = Boolean.TRUE;
               }
            }
         }
         else {
            highlight = Boolean.FALSE;
         }
      }
      else if (modelObject instanceof DbcProof) {
         if (action.isChecked()) {
            DbcProof proof = (DbcProof)modelObject;
            Iterator<DbcProofReference> iter = proof.getProofReferences().iterator();
            highlight = selectedModelElements.contains(modelObject);
            while (!highlight && iter.hasNext()) {
               DbcProofReference next = iter.next();
               if (selectedModelElements.contains(next) ||
                   selectedModelElements.contains(next.getTarget())) {
                  highlight = Boolean.TRUE;
               }
            }
         }
         else {
            highlight = Boolean.FALSE;
         }
      }
      else if (modelObject instanceof DbcProofReference) {
         DbcProofReference reference = (DbcProofReference)modelObject;
         highlight = action.isChecked() && (selectedModelElements.contains(reference) ||
                                            selectedModelElements.contains(reference.getSource()) ||
                                            selectedModelElements.contains(reference.getTarget()));
      }
      return highlight;
   }

   /**
    * Enables or disables the highlighting in the given {@link Object} if possible.
    * @param obj The {@link Object} to set highlighting.
    * @param highlight The new state to set.
    */
   protected void changeHighlightState(Object obj, boolean highlight) {
      if (obj instanceof DbcProof2EditPart) {
         DbcProof2EditPart part = (DbcProof2EditPart)obj;
         DbcProofFigure proofFigure = part.getPrimaryShape();
         if (highlight) {
            proofFigure.highlight(HIGHLIGHT_COLOR, HIGHLIGHT_LINE_WIDTH);
         }
         else {
            proofFigure.disableHighlighting();
         }
      }
      else if (obj instanceof DbcProofReferenceEditPart) {
         DbcProofReferenceEditPart part = (DbcProofReferenceEditPart)obj;
         DbcProofReferenceFigure partFigure = part.getPrimaryShape();
         if (highlight) {
            partFigure.highlight(HIGHLIGHT_COLOR, HIGHLIGHT_LINE_WIDTH);
         }
         else {
            partFigure.disableHighlighting();
         }
      }
      else if (obj instanceof DbcMethodEditPart) {
         DbcMethodEditPart part = (DbcMethodEditPart)obj;
         DbcMethodFigure partFigure = part.getPrimaryShape();
         if (highlight) {
            partFigure.highlight(HIGHLIGHT_COLOR, HIGHLIGHT_LINE_WIDTH);
         }
         else {
            partFigure.disableHighlighting();
         }
      }
      else if (obj instanceof DbcConstructorEditPart) {
         DbcConstructorEditPart part = (DbcConstructorEditPart)obj;
         DbcConstructorFigure partFigure = part.getPrimaryShape();
         if (highlight) {
            partFigure.highlight(HIGHLIGHT_COLOR, HIGHLIGHT_LINE_WIDTH);
         }
         else {
            partFigure.disableHighlighting();
         }
      }
      else if (obj instanceof DbcClass2EditPart) {
         DbcClass2EditPart part = (DbcClass2EditPart)obj;
         DbcClassFigure partFigure = part.getPrimaryShape();
         if (highlight) {
            partFigure.highlight(HIGHLIGHT_COLOR, HIGHLIGHT_LINE_WIDTH);
         }
         else {
            partFigure.disableHighlighting();
         }
      }
      else if (obj instanceof DbcInterface2EditPart) {
         DbcInterface2EditPart part = (DbcInterface2EditPart)obj;
         DbcInterfaceFigure partFigure = part.getPrimaryShape();
         if (highlight) {
            partFigure.highlight(HIGHLIGHT_COLOR, HIGHLIGHT_LINE_WIDTH);
         }
         else {
            partFigure.disableHighlighting();
         }
      }
      else if (obj instanceof DbcEnum2EditPart) {
         DbcEnum2EditPart part = (DbcEnum2EditPart)obj;
         DbcEnumFigure partFigure = part.getPrimaryShape();
         if (highlight) {
            partFigure.highlight(HIGHLIGHT_COLOR, HIGHLIGHT_LINE_WIDTH);
         }
         else {
            partFigure.disableHighlighting();
         }
      }
      else if (obj instanceof DbCAxiomContractEditPart) {
         DbCAxiomContractEditPart part = (DbCAxiomContractEditPart)obj;
         DbcAxiomContractFigure partFigure = part.getPrimaryShape();
         if (highlight) {
            partFigure.highlight(HIGHLIGHT_COLOR, HIGHLIGHT_LINE_WIDTH);
         }
         else {
            partFigure.disableHighlighting();
         }
      }
      else if (obj instanceof DbcOperationContractEditPart) {
         DbcOperationContractEditPart part = (DbcOperationContractEditPart)obj;
         DbcOperationContractFigure partFigure = part.getPrimaryShape();
         if (highlight) {
            partFigure.highlight(HIGHLIGHT_COLOR, HIGHLIGHT_LINE_WIDTH);
         }
         else {
            partFigure.disableHighlighting();
         }
      }
      else if (obj instanceof DbcAxiomEditPart) {
         DbcAxiomEditPart part = (DbcAxiomEditPart)obj;
         DbcAxiomFigure partFigure = part.getPrimaryShape();
         if (highlight) {
            partFigure.highlight(HIGHLIGHT_COLOR, HIGHLIGHT_LINE_WIDTH);
         }
         else {
            partFigure.disableHighlighting();
         }
      }
      else if (obj instanceof DbcInvariantEditPart) {
         DbcInvariantEditPart part = (DbcInvariantEditPart)obj;
         DbcInvariantFigure partFigure = part.getPrimaryShape();
         if (highlight) {
            partFigure.highlight(HIGHLIGHT_COLOR, HIGHLIGHT_LINE_WIDTH);
         }
         else {
            partFigure.disableHighlighting();
         }
      }
      else if (obj instanceof DbcAttributeEditPart) {
         DbcAttributeEditPart part = (DbcAttributeEditPart)obj;
         DbcAttributeFigure partFigure = part.getPrimaryShape();
         if (highlight) {
            partFigure.highlight(HIGHLIGHT_COLOR, HIGHLIGHT_LINE_WIDTH);
         }
         else {
            partFigure.disableHighlighting();
         }
      }
      else if (obj instanceof DbcEnumLiteralEditPart) {
         DbcEnumLiteralEditPart part = (DbcEnumLiteralEditPart)obj;
         DbcEnumLiteralFigure partFigure = part.getPrimaryShape();
         if (highlight) {
            partFigure.highlight(HIGHLIGHT_COLOR, HIGHLIGHT_LINE_WIDTH);
         }
         else {
            partFigure.disableHighlighting();
         }
      }
   }
}