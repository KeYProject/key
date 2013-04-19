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

package org.key_project.sed.ui.visualization.object_diagram.wizard;

import org.eclipse.core.runtime.Assert;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.object_diagram.provider.ObjectDiagramTypeProvider;
import org.key_project.util.java.IOUtil;

/**
 * A new wizard to create Object Diagrams.
 * @author Martin Hentschel
 */
public class NewObjectDiagramWizard extends AbstractObjectDiagramSaveAsWizard {
   /**
    * {@inheritDoc}
    */
   @Override
   protected String getInitialWindowTitle() {
      return "Create Object Diagram";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String getDiagramAndModelPageTitle() {
      return "Create Object Diagram";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Diagram getDiagramToSave(String fileName) {
      // Create empty diagram
      Diagram diagram = Graphiti.getPeCreateService().createDiagram(ObjectDiagramTypeProvider.TYPE, 
                                                                    IOUtil.getFileNameWithoutExtension(fileName), 
                                                                    true);
      Assert.isTrue(diagram.eResource() == null, "Diagram to save is already contained in a Resource.");
      ExecutionTreeUtil.createDomainAndResource(diagram); // Create Resource for the Diagram 
      return diagram;
   }
}