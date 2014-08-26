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

package org.key_project.key4eclipse.resources.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.key4eclipse.resources.test.testcase.junit.AutoDeleteTests;
import org.key_project.key4eclipse.resources.test.testcase.junit.BuilderTests;
import org.key_project.key4eclipse.resources.test.testcase.junit.HideMetaFilesTests;
import org.key_project.key4eclipse.resources.test.testcase.junit.KeYResourcesUtilTest;
import org.key_project.key4eclipse.resources.test.testcase.junit.MarkerTests;
import org.key_project.key4eclipse.resources.test.testcase.junit.ProjectInfoManagementTest;
import org.key_project.key4eclipse.resources.test.testcase.junit.ProofMetaFileContentExceptionTests;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   AutoDeleteTests.class,
   BuilderTests.class,
   HideMetaFilesTests.class,
   KeYResourcesUtilTest.class,
   MarkerTests.class,
   ProjectInfoManagementTest.class,
   ProofMetaFileContentExceptionTests.class
})
public class AllResourcesTests {
}