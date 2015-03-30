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

package org.key_project.sed.ui.visualization.object_diagram.util;

import java.util.List;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.mm.pictograms.Anchor;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.ui.IWorkbenchPage;
import org.key_project.sed.ui.visualization.model.od.AbstractODValueContainer;
import org.key_project.sed.ui.visualization.model.od.ODFactory;
import org.key_project.sed.ui.visualization.model.od.ODModel;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.object_diagram.perspective.StateVisualizationPerspectiveFactory;
import org.key_project.sed.ui.visualization.util.VisualizationPreferences;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

/**
 * Provides static methods for object diagrams.
 * @author Martin Hentschel
 */
public final class ObjectDiagramUtil {
   /**
    * Vertical offset used with diagram elements.
    */
   public static final int VERTICAL_OFFSET = 3;

   /**
    * Horizontal offset used with diagram elements.
    */
   public static final int HORIZONTAL_OFFSET = 10;

   /**
    * File extension for diagram file with included model.
    */
   public static final String DIAGRAM_AND_MODEL_FILE_EXTENSION = "od";

   /**
    * File extension for diagram file with included model with leading {@code '.'} character.
    */
   public static final String DIAGRAM_AND_MODEL_FILE_EXTENSION_WITH_DOT = "." + DIAGRAM_AND_MODEL_FILE_EXTENSION;

   /**
    * Forbid instances.
    */
   private ObjectDiagramUtil() {
   }
   
   /**
    * Checks if the given {@link Diagram} also has an {@link ODModel}.
    * @param diagram The {@link Diagram} to check.
    * @return {@code true} has model, {@code false} has no model.
    */
   public static boolean hasModel(Diagram diagram) {
      if (diagram != null && diagram.eResource() != null) {
         List<EObject> content = diagram.eResource().getContents();
         EObject modelCandidate = CollectionUtil.search(content, new IFilter<EObject>() {
            @Override
            public boolean select(EObject element) {
               return element instanceof ODModel;
            }
         });
         return modelCandidate != null;
      }
      else {
         return false;
      }
   }
   
   /**
    * Returns the {@link ODModel} which contains all business objects of
    * the given object diagram. If no one is available a new {@link ODModel} 
    * instance is created and add to the resource of the diagram.
    * @param diagram The {@link Diagram}.
    * @return The found or created {@link ODModel}.
    */
   public static ODModel getModel(Diagram diagram) {
      if (diagram != null && diagram.eResource() != null) {
         List<EObject> content = diagram.eResource().getContents();
         EObject modelCandidate = CollectionUtil.search(content, new IFilter<EObject>() {
            @Override
            public boolean select(EObject element) {
               return element instanceof ODModel;
            }
         });
         if (modelCandidate instanceof ODModel) {
            return (ODModel)modelCandidate;
         }
         else {
            ODModel newModel = ODFactory.eINSTANCE.createODModel();
            diagram.eResource().getContents().add(newModel);
            return newModel;
         }
      }
      else {
         return ODFactory.eINSTANCE.createODModel();
      }
   }

   /**
    * Returns the {@link AbstractODValueContainer} belonging to the anchor, or {@code null} if not available.
    * @param fp The {@link IFeatureProvider} to use.
    * @param anchor The {@link Anchor} to get its business object.
    * @return The found business object or {@code null} if not available.
    */
   public static AbstractODValueContainer getValueContainer(IFeatureProvider fp, Anchor anchor) {
      AbstractODValueContainer result = null;
      if (fp != null && anchor != null) {
         Object bo = fp.getBusinessObjectForPictogramElement(anchor.getParent());
         if (bo instanceof AbstractODValueContainer) {
            result = (AbstractODValueContainer)bo;
         }
      }
      return result;
   }

   /**
    * Returns the {@link ODObject} belonging to the anchor, or {@code null} if not available.
    * @param fp The {@link IFeatureProvider} to use.
    * @param anchor The {@link Anchor} to get its business object.
    * @return The found business object or {@code null} if not available.
    */
   public static ODObject getObject(IFeatureProvider fp, Anchor anchor) {
      ODObject result = null;
      if (fp != null && anchor != null) {
         Object bo = fp.getBusinessObjectForPictogramElement(anchor.getParent());
         if (bo instanceof ODObject) {
            result = (ODObject)bo;
         }
      }
      return result;
   }

   /**
    * Checks if a perspective switch to the state visualization perspective should be done.
    * @param activePage The currently active {@link IWorkbenchPage}.
    * @return {@code true} switch to state visualization perspective, {@code false} stay in current perspective.
    */
   public static boolean shouldSwitchToStateVisualizationPerspective(IWorkbenchPage activePage) {
      boolean switchPerspective = false;
      // Check if a different perspective is currently opened.
      if (!WorkbenchUtil.isPerspectiveOpen(StateVisualizationPerspectiveFactory.PERSPECTIVE_ID, activePage)) {
         String option = VisualizationPreferences.getSwitchToStateVisualizationPerspective();
         if (MessageDialogWithToggle.ALWAYS.equals(option)) {
            switchPerspective = true;
         }
         else if (MessageDialogWithToggle.NEVER.equals(option)) {
            switchPerspective = false;
         }
         else {
            MessageDialogWithToggle dialog = MessageDialogWithToggle.openYesNoQuestion(activePage.getActivePart().getSite().getShell(), 
                                                                                       "Confirm Perspective Switch", 
                                                                                       "The state visualization is associated with the " + WorkbenchUtil.getPerspectiveName(StateVisualizationPerspectiveFactory.PERSPECTIVE_ID) + " perspective.\n\nDo you want to open this perspective now?", 
                                                                                       null, 
                                                                                       false, 
                                                                                       VisualizationPreferences.getStore(), 
                                                                                       VisualizationPreferences.SWITCH_TO_STATE_VISUALIZATION_PERSPECTIVE);
            switchPerspective = (dialog.getReturnCode() == IDialogConstants.YES_ID);
         }
      }
      return switchPerspective;
   }
}