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

package de.hentschel.visualdbc.interactive.proving.ui.test.testCase;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.impl.EObjectImpl;
import org.junit.Test;
import org.key_project.util.test.util.TestUtilsUtil;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcmodelFactory;
import de.hentschel.visualdbc.generation.operation.CreateOperation;
import de.hentschel.visualdbc.generation.test.util.TestGenerationUtil;
import de.hentschel.visualdbc.interactive.proving.ui.util.DbcModelUtil;

/**
 * Tests for {@link DbcModelUtil}.
 * @author Martin Hentschel
 */
public class DbcModelUtilTest extends TestCase {
   /**
    * Tests {@link DbcModelUtil#getModelRoot(org.eclipse.emf.ecore.EObject)}
    */
   @Test
   public void testGetModelRoot() {
      IDSConnection connection = null;
      try {
         // Test null
         assertNull(DbcModelUtil.getModelRoot(null));
         // Test something invalid from other object
         assertNull(DbcModelUtil.getModelRoot(new EObjectImpl() {}));
         // Test not contained package
         assertNull(DbcModelUtil.getModelRoot(DbcmodelFactory.eINSTANCE.createDbcPackage()));
         // Test with dummy model
         connection = TestGenerationUtil.createDummyConnection();
         // Create target project
         IProject project = TestUtilsUtil.createProject("DbcModelUtilTest_testGetModelRoot");
         IFile modelFile = project.getFile("default.proof");
         IFile diagramFile = project.getFile("default.proof_diagram");
         // Create model
         CreateOperation co = new CreateOperation(connection, modelFile, diagramFile);
         co.execute(null, false);
         // Open model
         DbcModel model = TestGenerationUtil.openDbcModel(modelFile);
         // Compare created model with connection
         TestGenerationUtil.compareModel(connection, model);
         // Compare model elements
         assertEquals(model, DbcModelUtil.getModelRoot(model));
         TreeIterator<EObject> iter = model.eAllContents();
         while (iter.hasNext()) {
            assertEquals(model, DbcModelUtil.getModelRoot(iter.next()));
         }
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