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

package de.hentschel.visualdbc.statistic.ui.util;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.gef.EditPart;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.ocl.util.ObjectUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.DbcProofObligation;
import de.hentschel.visualdbc.dbcmodel.DbcProofStatus;
import de.hentschel.visualdbc.dbcmodel.IDbCProvable;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditor;
import de.hentschel.visualdbc.dbcmodel.diagram.util.GMFUtil;
import de.hentschel.visualdbc.dbcmodel.presentation.DbcmodelEditor;

/**
 * Provides static utility methods for the statistics.
 * @author Martin Hentschel
 */
public final class StatisticUtil {
   /**
    * Forbid instances.
    */
   private StatisticUtil() {
   }

   /**
    * Returns the column text for a {@link DbCProofObligation} defined by the column.
    * @param object The current row {@link Object}.
    * @param columnIndex The column index.
    * @param columnProofObligations The shown {@link DbCProofObligation}s in the columns.
    * @return The cell text.
    */
   public static String getColumnText(Object object, int columnIndex, List<DbcProofObligation> columnProofObligations) {
      DbcProofObligation obligation = getProofObligationForColumn(columnProofObligations, columnIndex);
      return getColumnText(object, obligation);
   }

   /**
    * Returns the column image for a {@link DbCProofObligation} defined by the column.
    * @param object The current row {@link Object}.
    * @param columnIndex The column index.
    * @param columnProofObligations The shown {@link DbCProofObligation}s in the columns.
    * @return The cell image.
    */
   public static Object getColumnImage(Object object, int columnIndex, List<DbcProofObligation> columnProofObligations) {
      DbcProofObligation obligation = getProofObligationForColumn(columnProofObligations, columnIndex);
      return getColumnImage(object, obligation);
   }

   /**
    * Returns the {@link DbCProofObligation} for the given column index
    * from the {@link List} of all shown {@link DbCProofObligation} in the columns.
    * @param columnProofObligations All shown {@link DbCProofObligation} in the columns.
    * @param columnIndex The column index.
    * @return The found {@link DbCProofObligation} or {@code null} if no {@link DbCProofObligation} is available.
    */
   public static DbcProofObligation getProofObligationForColumn(List<DbcProofObligation> columnProofObligations, int columnIndex) {
      if (columnProofObligations != null) {
         if (columnIndex - 1 < columnProofObligations.size()) {
            return columnProofObligations.get(columnIndex - 1);
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }

   /**
    * Returns the column text for a {@link DbCProofObligation} defined by the column.
    * @param object The current row {@link Object}.
    * @param obligation The available {@link DbCProofObligation}.
    * @return The cell text.
    */
   public static String getColumnText(Object object, DbcProofObligation obligation) {
      ProofStatus status = getProofStatus(object, obligation);
      return status != null ? status.getHumanText() : null;
   }

   /**
    * Returns the column image for a {@link DbCProofObligation} defined by the column.
    * @param object The current row {@link Object}.
    * @param obligation The available {@link DbCProofObligation}.
    * @return The cell image.
    */
   public static Object getColumnImage(Object object, DbcProofObligation obligation) {
      return null;
   }
   
   /**
    * Computes the {@link ProofStatus} for the given provable object
    * and for the defined proof obligation.
    * @param object The provable object.
    * @param obligation The proof obligation.
    * @return The computed {@link ProofStatus}.
    */
   public static ProofStatus getProofStatus(Object object, DbcProofObligation obligation) {
      ProofStatus result = null;
      if (object instanceof IDbCProvable) {
         IDbCProvable provable = (IDbCProvable)object;
         // Check if proof obligation is available
         if (provable.getProofObligations().contains(obligation)) {
            // Iterate over all proofs and compute the most important result
            result = ProofStatus.NOT_AVAILABLE;
            List<DbcProof> allProofs = provable.getAllProofs();
            for (DbcProof proof : allProofs) {
               // Check if the proof has the same obligation
               if (ObjectUtil.equal(proof.getObligation(), obligation.getObligation())) {
                  if (ProofStatus.FULFILLED.equals(result)) {
                     // Result is fulfilled, no need to change
                  }
                  else if (ProofStatus.OPEN.equals(result)) {
                     // Result is open, can only change to fulfilled
                     if (DbcProofStatus.FULFILLED.equals(proof.getStatus())) {
                        result = ProofStatus.FULFILLED;
                     }
                     else {
                        result = ProofStatus.OPEN;
                     }
                  }
                  else {
                     // Result is failed or don't exist, can only change to proof status
                     if (DbcProofStatus.OPEN.equals(proof.getStatus())) {
                        result = ProofStatus.OPEN;
                     }
                     else if (DbcProofStatus.FULFILLED.equals(proof.getStatus())) {
                        result = ProofStatus.FULFILLED;
                     }
                     else if (DbcProofStatus.FAILED.equals(proof.getStatus())) {
                        result = ProofStatus.FAILED;
                     }
                  }
               }
            }
         }
         else {
            result = ProofStatus.INVALID;
         }
      }
      return result;
   }
   
   /**
    * Possible proof status in the statistics.
    * @author Martin Hentschel
    */
   public static enum ProofStatus {
      /**
       * Proof obligation is not available on the provable.
       */
      INVALID,
      
      /**
       * No proof instance exists for the obligation.
       */
      NOT_AVAILABLE,
      
      /**
       * Proof is failed, no proofs are open or fulfilled.
       */
      FAILED,
      
      /**
       * At least one proof is open and no proof is fulfilled.
       */
      OPEN,
      
      /**
       * At least one proof is fulfilled.
       */
      FULFILLED;
      
      /**
       * Returns a human readable text.
       * @return The human readable text.
       */
      public String getHumanText() {
         switch (this) {
            case NOT_AVAILABLE : return "n. a.";
            case FAILED : return "failed";
            case OPEN : return "open";
            case FULFILLED : return "fulfilled";
            default : return null;
         }
      }
      
      /**
       * Returns the minimal {@link ProofStatus}.
       * @param statuses The given {@link ProofStatus} instances.
       * @return The minimal {@link ProofStatus}.
       */      
      public static ProofStatus min(ProofStatus... statuses) {
         ProofStatus min = ProofStatus.FULFILLED;
         for (ProofStatus status : statuses) {
            if (ProofStatus.FULFILLED.equals(min)) {
               if (ProofStatus.OPEN.equals(status) ||
                   ProofStatus.FAILED.equals(status) ||
                   ProofStatus.NOT_AVAILABLE.equals(status) ||
                   ProofStatus.INVALID.equals(status)) {
                  min = status;
               }
            }
            else if (ProofStatus.OPEN.equals(min)) {
               if (ProofStatus.FAILED.equals(status) ||
                   ProofStatus.NOT_AVAILABLE.equals(status) ||
                   ProofStatus.INVALID.equals(status)) {
                  min = status;
               }
            }
            else if (ProofStatus.FAILED.equals(min)) {
               if (ProofStatus.NOT_AVAILABLE.equals(status) ||
                   ProofStatus.INVALID.equals(status)) {
                  min = status;
               }
            }
            else if (ProofStatus.NOT_AVAILABLE.equals(min)) {
               if (ProofStatus.INVALID.equals(status)) {
                  min = status;
               }
            }
         }
         return min;
      }
   }

   /**
    * Selects the given elements in the given {@link DbcmodelEditor}.
    * @param editor The {@link DbcmodelEditor} to select elements in.
    * @param toSelect The elements to select.
    */
   public static void select(DbcmodelEditor editor, List<?> toSelect) {
      select(editor, SWTUtil.createSelection(toSelect));
   }

   /**
    * Selects the given elements in the given {@link DbcmodelEditor}.
    * @param editor The {@link DbcmodelEditor} to select elements in.
    * @param selection The elements to select.
    */
   public static void select(DbcmodelEditor editor, ISelection selection) {
      if (editor != null) {
         Viewer viewer = editor.getViewer();
         if (viewer != null) {
            viewer.setSelection(selection);
         }
      }
   }

   /**
    * Selects the given elements in the given {@link DbCDiagramEditor}.
    * @param editor The {@link DbCDiagramEditor} to select elements in.
    * @param selection The elements to select.
    */
   public static void select(DbCDiagramEditor editor, ISelection selection) {
      select(editor, SWTUtil.toList(selection));
   }

   /**
    * Selects the given elements in the given {@link DbCDiagramEditor}.
    * @param editor The {@link DbCDiagramEditor} to select elements in.
    * @param toSelect The elements to select.
    */
   public static void select(DbCDiagramEditor editor, List<?> toSelect) {
      if (editor != null && toSelect != null) {
         List<EditPart> partsToSelect = new LinkedList<EditPart>();
         // Find EditParts for the contained EObjects
         for (Object element : toSelect) {
            if (element instanceof EObject) {
               Collection<EditPart> parts = GMFUtil.findEditParts(editor.getDiagramEditPart(), (EObject)element);
               if (parts != null) {
                  for (EditPart part : parts) {
                     editor.getDiagramGraphicalViewer().reveal(part); // Make EditPart visible
                     partsToSelect.add(part);
                  }
               }
            }
         }
         // Select EditParts
         editor.getDiagramGraphicalViewer().setSelection(SWTUtil.createSelection(partsToSelect));
      }
   }
}