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

package org.key_project.sed.ui.visualization.execution_tree.wizard;

import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.util.java.IOUtil;

/**
 * A new wizard to create Symbolic Execution Tree Diagrams.
 * @author Martin Hentschel
 */
public class NewExecutionTreeDiagramWizard extends AbstractExecutionTreeDiagramSaveAsWizard {
   /**
    * {@inheritDoc}
    */
   @Override
   protected ISEDDebugTarget[] getDebugTargetsToSave() {
      return new ISEDDebugTarget[0];
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Diagram getDiagramToSave() {
      return Graphiti.getPeCreateService().createDiagram(ExecutionTreeDiagramTypeProvider.TYPE, 
                                                         IOUtil.getFileNameWithoutExtension(getDiagramPage().getFileName()), 
                                                         true);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getInitialWindowTitle() {
      return "Create Symbolic Execution Tree Diagram";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getDiagramPageTitle() {
      return "Create Symbolic Execution Tree Diagram";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getModelPageTitle() {
      return "Create Symbolic Execution Tree Domain Model";
   }
}