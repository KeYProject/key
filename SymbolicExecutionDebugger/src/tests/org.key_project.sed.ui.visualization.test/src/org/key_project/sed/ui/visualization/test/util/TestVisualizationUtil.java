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

package org.key_project.sed.ui.visualization.test.util;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.charset.Charset;
import java.util.Collections;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.transaction.RecordingCommand;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.ui.services.GraphitiUi;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IPropertyListener;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.serialization.SEXMLWriter;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.view.ExecutionTreeView;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Provides static methods that make testing easier.
 * @author Martin Hentschel
 */
public final class TestVisualizationUtil {
   /**
    * Forbid instances.
    */
   private TestVisualizationUtil() {
   }
   
   /**
    * Creates an empty execution tree diagram.
    * @param diagramFile The diagram file.
    * @param modelFile The model file.
    * @return The created {@link Diagram}.
    * @throws CoreException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public static Diagram createEmptyExecutionTreeDiagram(IFile diagramFile, IFile modelFile) throws CoreException, IOException {
      TestCase.assertNotNull(diagramFile);
      TestCase.assertNotNull(modelFile);
      // Create model file
      SEXMLWriter writer = new SEXMLWriter();
      String modelContent = writer.toXML(new ISEDebugTarget[0], "UTF-8", false, false, false, null);
      if (!modelFile.exists()) {
         modelFile.create(new ByteArrayInputStream(modelContent.getBytes(Charset.forName("UTF-8"))), true, null);
      }
      else {
         modelFile.setContents(new ByteArrayInputStream(modelContent.getBytes(Charset.forName("UTF-8"))), true, true, null);
      }
      // Create diagram file
      final Diagram diagram = Graphiti.getPeCreateService().createDiagram(ExecutionTreeDiagramTypeProvider.TYPE, "Test", true);
      URI diagramURI = URI.createPlatformResourceURI(diagramFile.getFullPath().toString(), true);
      TransactionalEditingDomain domain = GraphitiUtil.createDomainAndResource(diagram, diagramURI); 
      final URI domainURI = URI.createPlatformResourceURI(modelFile.getFullPath().toString(), true);
      domain.getCommandStack().execute(new RecordingCommand(domain, "Set link to model file.") {
         @Override
         protected void doExecute() {
            GraphitiUi.getPeService().setPropertyValue(diagram, ExecutionTreeUtil.USER_PROPERTY_DOMAIN_MODEL_FILE, domainURI.toString());
         }

         @Override
         public boolean canUndo() {
            return false;
         }
      });
      diagram.eResource().save(Collections.EMPTY_MAP);
      return diagram;
   }

   /**
    * Returns the {@link SWTBotView} for the Symbolic Execution Tree view.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @return The {@link SWTBotView}.
    */
   public static SWTBotView getSymbolicExecutionTreeView(SWTWorkbenchBot bot) {
      return bot.viewById(ExecutionTreeView.VIEW_ID);
   }

   /**
    * Sets the focus to the symbolic execution tree view.
    */
   public static void setFocusToSymbolicExecutionTreeView() {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotView setView = TestVisualizationUtil.getSymbolicExecutionTreeView(bot);
      setView.setFocus();
      TestUtilsUtil.sleep(500); // A short delay to ensure that properties view is also updated
      TestUtilsUtil.waitForJobs();
   }

   /**
    * Returns the {@link SWTBotGefEditor} for the Graphiti Editor in {@link #getSymbolicExecutionTreeView(SWTWorkbenchBot)}.
    * @param bot The {@link SWTWorkbenchBot} to use.
    * @return The {@link SWTBotGefEditor}.
    */
   public static SWTBotGefEditor getSymbolicExecutionTreeViewGefEditor(SWTWorkbenchBot bot) {
      SWTBotView botView = getSymbolicExecutionTreeView(bot);
      final ExecutionTreeView view = (ExecutionTreeView) botView.getReference().getView(true);
      IEditorReference dummyReference = new IEditorReference() {
         @Override
         public void removePropertyListener(IPropertyListener listener) {
         }
         
         @Override
         public void removePartPropertyListener(IPropertyChangeListener listener) {
         }
         
         @Override
         public boolean isDirty() {
            return getEditor(false).isDirty();
         }
         
         @Override
         public String getTitleToolTip() {
            return getEditor(false).getTitleToolTip();
         }
         
         @Override
         public Image getTitleImage() {
            return getEditor(false).getTitleImage();
         }
         
         @Override
         public String getTitle() {
            return getEditor(false).getTitle();
         }
         
         @Override
         public String getPartProperty(String key) {
            return null;
         }
         
         @Override
         public String getPartName() {
            return null;
         }
         
         @Override
         public IWorkbenchPart getPart(boolean restore) {
            return getEditor(restore);
         }
         
         @Override
         public IWorkbenchPage getPage() {
            return getEditor(false).getSite().getPage();
         }
         
         @Override
         public String getId() {
            return getEditor(false).getSite().getId();
         }
         
         @Override
         public String getContentDescription() {
            return null;
         }
         
         @Override
         public void addPropertyListener(IPropertyListener listener) {
         }
         
         @Override
         public void addPartPropertyListener(IPropertyChangeListener listener) {
         }
         
         @Override
         public boolean isPinned() {
            return false;
         }
         
         @Override
         public String getName() {
            return null;
         }
         
         @Override
         public String getFactoryId() {
            return null;
         }
         
         @Override
         public IEditorInput getEditorInput() throws PartInitException {
            return getEditor(false).getEditorInput();
         }
         
         @Override
         public IEditorPart getEditor(boolean restore) {
            return view.getEditorPart();
         }
      };
      return new SWTBotGefEditor(dummyReference, bot);
   }
}