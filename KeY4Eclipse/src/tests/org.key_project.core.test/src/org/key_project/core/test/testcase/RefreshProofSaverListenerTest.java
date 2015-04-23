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

package org.key_project.core.test.testcase;

import java.io.File;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.junit.Test;
import org.key_project.core.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;

/**
 * Tests for {@code org.key_project.key4eclipse.event.RefreshProofSaverListener}.
 * @author Martin Hentschel
 */
public class RefreshProofSaverListenerTest extends TestCase {
   /**
    * Tests if an {@link IFile} is refreshed when its local file changes
    * via {@link ProofSaver#save()}.
    */
   @Test
   public void testRefresh() throws Exception {
      // Create file
      IProject project = TestUtilsUtil.createProject("RefreshProofSaverListenerTest_testRefresh");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/SimpleProof", project);
      IFile proofFile = project.getFile("SimpleProof.proof");
      IFile file = TestUtilsUtil.createFile(project, "Test.proof", "Replace me!");
      File location = ResourceUtil.getLocation(file);
      // Do proof
      KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(ResourceUtil.getLocation(proofFile), null, null, null);
      try {
         Proof proof = env.getLoadedProof();
         assertNotNull(proof);
         // Save proof
         new ProofSaver(proof, location.getAbsolutePath(), "1.0").save();
         // Make sure that IFile was updated
         assertTrue(file.isSynchronized(IResource.DEPTH_INFINITE));
         assertFalse("Replace me!".equals(ResourceUtil.readFrom(file)));
      }
      finally {
         env.dispose();
      }
   }
}