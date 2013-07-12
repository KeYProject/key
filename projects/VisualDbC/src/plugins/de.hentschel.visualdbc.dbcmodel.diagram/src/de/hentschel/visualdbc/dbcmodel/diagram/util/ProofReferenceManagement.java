package de.hentschel.visualdbc.dbcmodel.diagram.util;

import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.gef.EditPart;
import org.eclipse.gmf.runtime.diagram.ui.parts.DiagramEditor;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;

import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.IDbCProofReferencable;
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
 * Provides static methods to update the proof reference management
 * of a {@link DiagramEditor}.
 * @author Martin Hentschel
 * @generated NOT
 */
public class ProofReferenceManagement {
   /**
    * The parameter to show all proof references.
    */
   public static final String SHOW_ALL = "Show All";

   /**
    * The parameter to show only selected proof references.
    */
   public static final String SHOW_SELECTED = "Show Selected";

   /**
    * The parameter to hide all proof references.
    */
   public static final String HIDE_ALL = "Hide All";
   
   /**
    * The {@link Color} which is used for highlighting.
    */
   public static final Color HIGHLIGHT_COLOR = new Color(Display.getDefault(), 52, 80, 116);
   
   /**
    * The line width used for highlighting.
    */
   public static final int HIGHLIGHT_LINE_WIDTH = 3;

   /**
    * Hides or shows the {@link EditPart} of {@link DbcProofReference}
    * in the given {@link DiagramEditor}. 
    * @param targetEditor The {@link DiagramEditor} to update.
    * @param selection The selection with the proof references to show.
    * @param showHideValue The value which defines which proof references should be shown and which one not.
    */
   public static void updateHiddenElements(IEditorPart targetEditor, 
                                           ISelection selection, 
                                           Object showHideValue) {
      if (targetEditor instanceof DiagramEditor && 
          selection instanceof IStructuredSelection &&
          showHideValue != null) {
         DiagramEditor editor = (DiagramEditor)targetEditor;
         List<?> selectedElements = ((IStructuredSelection)selection).toList();
         Map<?, ?> map = editor.getDiagramGraphicalViewer().getEditPartRegistry();
         // Iterate over all EditParts of the diagram
         for (Object obj : map.values()) {
            if (obj instanceof DbcProofReferenceEditPart) {
               DbcProofReferenceEditPart part = (DbcProofReferenceEditPart)obj;
               if (part.getFigure() instanceof DbcProofReferenceFigure) {
                  DbcProofReferenceFigure partFigure = (DbcProofReferenceFigure)part.getFigure();
                  // Compute visibility based on the ID of the given action.
                  boolean visible;
                  if (SHOW_SELECTED.equals(showHideValue)) {
                     visible = selectedElements.contains(part) ||
                               selectedElements.contains(part.getTarget()) ||
                               selectedElements.contains(part.getSource());
                  }
                  else if (HIDE_ALL.equals(showHideValue)) {
                     visible = false;
                  }
                  else {
                     visible = true;
                  }
                  // Update 
                  part.getFigure().setVisible(visible); // Update visibility flag to cause a repaint
                  partFigure.setGlobalVisible(visible); // Set global visibility because setVisible() is updated from time to time, e.g. during scroling
               }
            }
         }
      }
   }

   /**
    * Highlights elements based on the selected elements in context
    * of proof references.
    * @param targetEditor The {@link DiagramEditor} to update.
    * @param selection The selection with the proof references to show.
    * @param highlightState Defines if highlighting should be used or not.
    */
   public static void updateHighlighting(IEditorPart targetEditor, 
                                         ISelection selection, 
                                         Object highlightState) {
      if (targetEditor instanceof DiagramEditor && 
          selection instanceof IStructuredSelection && 
          highlightState != null) {
         DiagramEditor editor = (DiagramEditor)targetEditor;
         List<?> selectedElements = ((IStructuredSelection)selection).toList();
         List<?> selectedModelElements = GMFUtil.getModelObjects(selectedElements);
         Map<?, ?> map = editor.getDiagramGraphicalViewer().getEditPartRegistry();
         // Iterate over all EditParts of the diagram
         for (Object obj : map.values()) {
            if (obj instanceof EditPart) {
               // Compute highlight state
               Object modelObject = GMFUtil.getModelObject((EditPart)obj);
               Boolean highlight = shouldHighlight(modelObject, "true".equals(highlightState.toString()), selectedModelElements);
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
    * @param highlight The highlight state to set.
    * @param selectedModelElements The currently selected model elements.
    * @return {@code Boolean#TRUE} = highlight, {@code Boolean#FALSE} = do not highlight, {@code null} never highlight.
    */
   protected static Boolean shouldHighlight(Object modelObject, boolean highlight, List<?> selectedModelElements) {
      Boolean result = null;
      if (modelObject instanceof IDbCProofReferencable) {
         if (highlight) {
            IDbCProofReferencable referencable = (IDbCProofReferencable)modelObject;
            Iterator<DbcProofReference> iter = referencable.getAllReferences().iterator();
            result = selectedModelElements.contains(modelObject);
            while (!result && iter.hasNext()) {
               DbcProofReference next = iter.next();
               if (selectedModelElements.contains(next) ||
                   selectedModelElements.contains(next.getSource())) {
                  result = Boolean.TRUE;
               }
            }
         }
         else {
            result = Boolean.FALSE;
         }
      }
      else if (modelObject instanceof DbcProof) {
         if (highlight) {
            DbcProof proof = (DbcProof)modelObject;
            Iterator<DbcProofReference> iter = proof.getProofReferences().iterator();
            result = selectedModelElements.contains(modelObject);
            while (!result && iter.hasNext()) {
               DbcProofReference next = iter.next();
               if (selectedModelElements.contains(next) ||
                   selectedModelElements.contains(next.getTarget())) {
                  result = Boolean.TRUE;
               }
            }
         }
         else {
            result = Boolean.FALSE;
         }
      }
      else if (modelObject instanceof DbcProofReference) {
         DbcProofReference reference = (DbcProofReference)modelObject;
         result = highlight && (selectedModelElements.contains(reference) ||
                                selectedModelElements.contains(reference.getSource()) ||
                                selectedModelElements.contains(reference.getTarget()));
      }
      return result;
   }

   /**
    * Enables or disables the highlighting in the given {@link Object} if possible.
    * @param obj The {@link Object} to set highlighting.
    * @param highlight The new state to set.
    */
   protected static void changeHighlightState(Object obj, boolean highlight) {
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
