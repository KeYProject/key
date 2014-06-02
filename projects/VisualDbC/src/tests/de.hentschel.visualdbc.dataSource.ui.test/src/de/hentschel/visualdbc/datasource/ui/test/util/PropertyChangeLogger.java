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

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.LinkedList;
import java.util.List;

/**
 * Implementation of {@link PropertyChangeListener} that logs all events
 * in the main memory.
 * @author Martin Hentschel
 */
public class PropertyChangeLogger implements PropertyChangeListener {
   /**
    * All logged events.
    */
   private List<PropertyChangeEvent> log = new LinkedList<PropertyChangeEvent>();

   /**
    * {@inheritDoc}
    */
   @Override
   public void propertyChange(PropertyChangeEvent e) {
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
   public List<PropertyChangeEvent> getLog() {
      return log;
   }
}