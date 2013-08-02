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

package de.hentschel.visualdbc.datasource.ui.setting;

import java.util.LinkedList;
import java.util.List;

import de.hentschel.visualdbc.datasource.ui.setting.event.ISettingControlListener;
import de.hentschel.visualdbc.datasource.ui.setting.event.SettingControlEvent;

/**
 * Provides a basic implementation of {@link ISettingControl}.
 * @author Martin Hentschel
 */
public abstract class AbstractSettingControl implements ISettingControl {
   /**
    * All registered listeners.
    */
   private List<ISettingControlListener> listeners = new LinkedList<ISettingControlListener>();
   
   /**
    * Fires the value change event to all listeners.
    * @param e The event to fire.
    */
   protected void fireValueChanged(SettingControlEvent e) {
      ISettingControlListener[] allListeners = getSettingControlListeners();
      for (ISettingControlListener l : allListeners) {
         l.valueChanged(e);
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addSettingControlListener(ISettingControlListener l) {
      if (l != null) {
         listeners.add(l);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeSettingControlListener(ISettingControlListener l) {
      if (l != null) {
         listeners.remove(l);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISettingControlListener[] getSettingControlListeners() {
      return listeners.toArray(new ISettingControlListener[listeners.size()]);
   }
}