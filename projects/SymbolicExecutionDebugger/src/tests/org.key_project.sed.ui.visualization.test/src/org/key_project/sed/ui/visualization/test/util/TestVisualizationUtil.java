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
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.serialization.SEDXMLWriter;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.view.ExecutionTreeView;

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
      SEDXMLWriter writer = new SEDXMLWriter();
      String modelContent = writer.toXML(new ISEDDebugTarget[0], "UTF-8", false, false, false, null);
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
   }
}