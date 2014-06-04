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

package org.key_project.util.test.view;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.eclipse.graphiti.ui.editor.DiagramEditorActionBarContributor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.part.FileEditorInput;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.view.editorInView.AbstractEditorInViewView;
import org.key_project.util.test.Activator;
import org.key_project.util.test.testcase.swtbot.SWTBotAbstractEditorInViewViewTest;

/**
 * Implementation of {@link IViewPart} which shows the Graphiti Editor
 * {@link DiagramEditor} as content. The view is used in test case
 * {@link SWTBotAbstractEditorInViewViewTest}.
 * @author Martin Hentschel
 */
public class GraphitiEditorInViewView extends AbstractEditorInViewView<DiagramEditor, DiagramEditorActionBarContributor> {
   /**
    * The ID of this view.
    */
   public static final String VIEW_ID = "org.key_project.util.test.view.GraphitiEditorInViewView";
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected DiagramEditor createEditorPart() {
      return new DiagramEditor();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected DiagramEditorActionBarContributor createEditorActionBarContributor() {
      return new DiagramEditorActionBarContributor();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IEditorInput createEditorInput() {
      try {
         IProject project = ResourcesPlugin.getWorkspace().getRoot().getProject("GraphitiEditorInViewView");
         if (!project.exists()) {
            project.create(null);
         }
         if (!project.isOpen()) {
            project.open(null);
         }
         IFile file = project.getFile("ExampleGraphitiTutorialDiagram.diagram");
         if (!file.exists()) {
            BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/graphiti/ExampleGraphitiTutorialDiagram", project);
         }
         return new FileEditorInput(file);
      }
      catch (Exception e) {
         throw new RuntimeException(e);
      }
   }
}