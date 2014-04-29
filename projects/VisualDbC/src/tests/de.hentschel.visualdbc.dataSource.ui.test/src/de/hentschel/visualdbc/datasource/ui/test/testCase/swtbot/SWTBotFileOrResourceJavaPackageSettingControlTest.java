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

package de.hentschel.visualdbc.datasource.ui.test.testCase.swtbot;

import org.eclipse.jdt.core.IJavaElement;

/**
 * SWT Bot tests for file or resource java package settings controls.
 * @author Martin Hentschel
 */
public class SWTBotFileOrResourceJavaPackageSettingControlTest extends SWTBotJavaPackageSettingControlTest {
   /**
    * {@inheritDoc}
    */
   @Override
   protected Object getExpectedPackage(IJavaElement element) {
      return element.getPath();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected String getControlId() {
      return "de.hentschel.visualdbc.datasource.ui.setting.FileOrResourceJavaPackageSettingControl";
   }
}