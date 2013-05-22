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

import java.util.List;
import java.util.Map;

import org.eclipse.draw2d.IFigure;
import org.eclipse.gef.EditPart;
import org.eclipse.gmf.runtime.diagram.ui.parts.DiagramEditor;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.hentschel.visualdbc.dbcmodel.DbcProofReference;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofReferenceEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcProofReferenceEditPart.DbcProofReferenceFigure;

/**
 * <p>
 * This {@link IEditorActionDelegate} contains the whole functionality
 * for the automatic proof reference hiding feature. It provides the following modes:
 * <ul>
 *    <li>Show all proof references</li>
 *    <li>Show only proof references of selected elements (incoming/outgoing references or references itself)</li>
 *    <li>Hide all proof references</li>
 * </ul>
 * </p>
 * <p>
 * The plugin.xml file registers this {@link IEditorActionDelegate} three
 * times for each mode with different ids 
 * ({@link #SHOW_ID}, {@value #SHOW_SELECTED_ID} and {@link #HIDE_ID}). 
 * The only checked one is responsible to hide or show references in the diagram
 * while not checked ones do nothing.
 * </p>
 * <p>
 * The hiding is implemented by setting the visibility of an {@link IFigure}
 * which is contained in an {@link EditPart}. To make sure that the state
 * is not changed automatically, e.g. during scrolling the special
 * {@link DbcProofReferenceFigure} contains a global visibility flag which
 * is also changed accordingly. The alternative solution to set the visibility
 * in the diagram model of GMF ({@link View}) is not possible because it is
 * saved in the diagram file, influences the Undo/Redo history and causes
 * problems when files are reloaded because invisible {@link View}s are not 
 * accessible any more.
 * </p>
 * @author Martin Hentschel
 */
public class AutomaticProofReferenceHidingEditorActionDelegate implements IEditorActionDelegate {
   /**
    * The ID of the action which enables the automatic proof reference hiding mode: Show all
    */
   public static final String SHOW_ID = "de.hentschel.visualdbc.dbcmodel.diagram.custom.showProofReferences";

   /**
    * The ID of the action which enables the automatic proof reference hiding mode: Show selected only
    */
   public static final String SHOW_SELECTED_ID = "de.hentschel.visualdbc.dbcmodel.diagram.custom.showSelectedProofReferences";

   /**
    * The ID of the action which enables the automatic proof reference hiding mode: Show none
    */
   public static final String HIDE_ID = "de.hentschel.visualdbc.dbcmodel.diagram.custom.hideProofReferences";

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
      updateHiddenElements(action);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void selectionChanged(IAction action, ISelection selection) {
      this.selection = selection;
      updateHiddenElements(action);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setActiveEditor(final IAction action, IEditorPart targetEditor) {
      this.targetEditor = targetEditor;
      this.selection = null;
      updateHiddenElements(action);
   }

   /**
    * Hides or shows the {@link EditPart} of {@link DbcProofReference}
    * in the given {@link DiagramEditor}. 
    * @param action The {@link IAction} which enables/disables the automatic proof reference hiding.
    */
   protected void updateHiddenElements(IAction action) {
      if (action.isChecked()) { // Do only something if the action is selected.
         if (targetEditor instanceof DiagramEditor) {
            DiagramEditor editor = (DiagramEditor)targetEditor;
            List<?> selectedElements = SWTUtil.toList(selection);
            Map<?, ?> map = editor.getDiagramGraphicalViewer().getEditPartRegistry();
            // Iterate over all EditParts of the diagram
            for (Object obj : map.values()) {
               if (obj instanceof DbcProofReferenceEditPart) {
                  DbcProofReferenceEditPart part = (DbcProofReferenceEditPart)obj;
                  if (part.getFigure() instanceof DbcProofReferenceFigure) {
                     DbcProofReferenceFigure partFigure = (DbcProofReferenceFigure)part.getFigure();
                     // Compute visibility based on the ID of the given action.
                     boolean visible;
                     if (SHOW_SELECTED_ID.equals(action.getId())) {
                        visible = selectedElements.contains(part) ||
                                  selectedElements.contains(part.getTarget()) ||
                                  selectedElements.contains(part.getSource());
                     }
                     else if (HIDE_ID.equals(action.getId())) {
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
   }
}