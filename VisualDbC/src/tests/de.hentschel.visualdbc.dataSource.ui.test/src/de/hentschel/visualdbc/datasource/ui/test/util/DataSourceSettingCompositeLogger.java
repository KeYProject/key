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

package de.hentschel.visualdbc.datasource.ui.test.util;

import java.util.LinkedList;
import java.util.List;

import de.hentschel.visualdbc.datasource.ui.composite.event.DataSourceSettingCompositeEvent;
import de.hentschel.visualdbc.datasource.ui.composite.event.IDataSourceSettingCompositeListener;

/**
 * Implementation of {@link IDataSourceSettingCompositeListener} that logs all events
 * in the main memory.
 * @author Martin Hentschel
 */
public class DataSourceSettingCompositeLogger implements IDataSourceSettingCompositeListener {
   /**
    * All logged events.
    */
   private List<DataSourceSettingCompositeEvent> log = new LinkedList<DataSourceSettingCompositeEvent>();

   /**
    * {@inheritDoc}
    */
   @Override
   public void settingValueChanged(DataSourceSettingCompositeEvent e) {
      log.add(e);
   }
   
   /**
    * Clears the log.
    */
   public void clear() {
      log.clear();
   }

   /**
    * Returns the logged events.
    * @return The logged events.
    */
   public List<DataSourceSettingCompositeEvent> getLog() {
      return log;
   }   
}