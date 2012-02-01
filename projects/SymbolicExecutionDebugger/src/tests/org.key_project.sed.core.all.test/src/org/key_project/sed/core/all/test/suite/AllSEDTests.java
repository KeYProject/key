/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package org.key_project.sed.core.all.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.key4eclipse.starter.core.test.suite.AllStarterCoreTests;
import org.key_project.key4eclipse.suite.AllKeY4EclipseTests;
import org.key_project.key4eclipse.util.test.suite.AllUtilTests;
import org.key_project.sed.key.core.test.suite.AllSEDKeYTests;
import org.key_project.sed.key.ui.test.suite.AllSEDKeYUITests;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    AllKeY4EclipseTests.class,
    AllUtilTests.class,
    AllStarterCoreTests.class,
    AllSEDKeYTests.class,
    AllSEDKeYUITests.class
})
public class AllSEDTests {
}
