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

package de.hentschel.visualdbc.interactive.proving.ui.test.testCase;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.junit.Test;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.test.dummyModel.DummyModelDriver;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.generation.operation.CreateOperation;
import de.hentschel.visualdbc.generation.test.util.TestGenerationUtil;
import de.hentschel.visualdbc.interactive.proving.ui.finder.DefaultDbcFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.DefaultDbcFinderFactory;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDbcFinder;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDbcFinderFactory;
import de.hentschel.visualdbc.interactive.proving.ui.test.util.TestInteractiveProvingUtil;

/**
 * Tests for {@link DefaultDbcFinder}.
 * @author Martin Hentschel
 */
public class DefaultDbcFinderTest extends TestCase {
   /**
    * Searches every element in the {@link DummyModelDriver}.
    */
   @Test
   public void testDummyModel() {
      IDSConnection connection = null;
      try {
         // Open connection
         connection = TestGenerationUtil.createDummyConnection();
         // Create target project
         IProject project = TestUtilsUtil.createProject("DefaultDbcFinderTest_testDummyModel");
         IFile modelFile = project.getFile("default.proof");
         IFile diagramFile = project.getFile("default.proof_diagram");
         // Create model
         CreateOperation co = new CreateOperation(connection, modelFile, diagramFile);
         co.execute(null, false);
         // Open model
         DbcModel model = TestGenerationUtil.openDbcModel(modelFile);
         // Compare created model with connection
         TestGenerationUtil.compareModel(connection, model);
         // Create finder
         IDbcFinderFactory factory = new DefaultDbcFinderFactory();
         assertTrue(factory.canHandle(connection));
         IDbcFinder finder = factory.createFinder(model);
         assertTrue(finder instanceof DefaultDbcFinder);
         // Search all elements
         TestInteractiveProvingUtil.findAllElements(connection, finder);
      }
      catch (CoreException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      catch (DSException e) {
         e.printStackTrace();
         fail(e.getMessage());
      }
      finally {
         TestGenerationUtil.closeConnection(connection);
      }
   }
}