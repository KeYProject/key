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

package de.hentschel.visualdbc.datasource.ui.test.dataSource;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.hentschel.visualdbc.datasource.model.IDSConnectionSetting;
import de.hentschel.visualdbc.datasource.model.memory.MemoryConnectionSetting;

/**
 * A dummy driver that provides some setting controls.
 * @author Martin Hentschel
 */
public class UIDummyDriverB extends UIDummyDriverA {
   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSConnectionSetting> getConnectionSettings() {
      List<IDSConnectionSetting> result = new LinkedList<IDSConnectionSetting>();
      result.add(new MemoryConnectionSetting(SETTING_BOOLEAN, "Boolean from " + getName(), "de.hentschel.visualdbc.datasource.ui.setting.BooleanSettingControl") {
         @Override
         public Object getInitialValue(ISelection selection) {
            return Boolean.FALSE;
         }
      });
      result.add(new MemoryConnectionSetting(SETTING_RESOURCE_PACKAGE, "Resource Package", "de.hentschel.visualdbc.datasource.ui.setting.FileOrResourceJavaPackageSettingControl") {
         @Override
         public Object getInitialValue(ISelection selection) {
            return selection instanceof IStructuredSelection ? ((IStructuredSelection)selection).getFirstElement() : null;
         }
      });
      return result;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "B-Dummy-Driver";
   }
}