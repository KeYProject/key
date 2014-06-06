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

package org.key_project.sed.ui.visualization.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.ui.visualization.test.testcase.AbsoluteFileSystemPathSourceContainerTest;
import org.key_project.sed.ui.visualization.test.testcase.AbstractDebugViewBasedEditorInViewViewTest;
import org.key_project.sed.ui.visualization.test.testcase.EditableMultiDeleteInfoTest;
import org.key_project.sed.ui.visualization.test.testcase.ExecutionTreeUtilTest;
import org.key_project.sed.ui.visualization.test.testcase.GraphitiUtilTest;
import org.key_project.sed.ui.visualization.test.testcase.LogUtilTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   AbsoluteFileSystemPathSourceContainerTest.class,
   AbstractDebugViewBasedEditorInViewViewTest.class,
   EditableMultiDeleteInfoTest.class,
   ExecutionTreeUtilTest.class,
   GraphitiUtilTest.class,
   LogUtilTest.class
})
public class AllSEDUIVisualizationTests {
}