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

package de.hentschel.visualdbc.datasource.ui.setting.event;

import java.util.EventObject;

import org.eclipse.core.runtime.Assert;

import de.hentschel.visualdbc.datasource.ui.setting.ISettingControl;

/**
 * An event thrown from an {@link ISettingControl}.
 * @author Martin Hentschel
 */
public class SettingControlEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = 1009229582492880675L;

   /**
    * The new value.
    */
   private Object newValue;

   /**
    * The validation message or {@code null} if the value is valid.
    */
   private String validationMessage;
   
   /**
    * Constructor.
    * @param source The source that has thrown this event.
    * @param newValue The new value.
    * @param validationMessage The validation message or {@code null} if the value is valid.
    */
   public SettingControlEvent(ISettingControl source, 
                              Object newValue, 
                              String validationMessage) {
      super(source);
      Assert.isNotNull(source);
      this.newValue = newValue;
      this.validationMessage = validationMessage;
   }
   
   /**
    * Returns the new value.
    * @return The new value.
    */
   public Object getNewValue() {
      return newValue;
   }
   
   /**
    * Returns the the validation message or {@code null} if the value is valid.
    * @return The validation message or {@code null} if the value is valid.
    */
   public String getValidationMessage() {
      return validationMessage;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISettingControl getSource() {
      return (ISettingControl)super.getSource();
   }
}