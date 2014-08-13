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

package org.key_project.key4eclipse.all.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.key4eclipse.common.ui.test.suite.AllCommonUiTests;
import org.key_project.key4eclipse.starter.core.test.suite.AllStarterCoreTests;
import org.key_project.key4eclipse.starter.ui.test.suite.AllStarterUITests;
import org.key_project.key4eclipse.test.suite.AllKeY4EclipseTests;
import org.key_project.util.test.suite.AllUtilTests;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   AllKeY4EclipseTests.class,
   AllUtilTests.class,
   AllStarterCoreTests.class,
   AllCommonUiTests.class,
   AllStarterUITests.class
})
public class AllTests {
}