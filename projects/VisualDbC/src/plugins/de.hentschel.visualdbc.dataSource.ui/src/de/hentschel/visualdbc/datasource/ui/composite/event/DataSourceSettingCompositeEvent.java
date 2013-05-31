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

package de.hentschel.visualdbc.datasource.ui.composite.event;

import java.util.EventObject;

import org.eclipse.core.runtime.Assert;

import de.hentschel.visualdbc.datasource.ui.composite.DataSourceSettingComposite;
import de.hentschel.visualdbc.datasource.ui.setting.ISettingControl;

/**
 * An event thrown from the {@link DataSourceSettingComposite}.
 * @author Martin Hentschel
 */
public class DataSourceSettingCompositeEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = -8027314525619613935L;
   
   /**
    * The new value.
    */
   private Object newValue;
   
   /**
    * The changed setting control.
    */
   private ISettingControl settingsControl;

   /**
    * The validation message or {@code null} if the value is valid.
    */
   private String validationMessage;
   
   /**
    * Constructor.
    * @param source The source that has thrown this event.
    * @param settingsControl The changed setting control.
    * @param newValue The new value.
    * @param validationMessage The validation message or {@code null} if the value is valid.
    */
   public DataSourceSettingCompositeEvent(DataSourceSettingComposite source, 
                                          ISettingControl settingsControl, 
                                          Object newValue, 
                                          String validationMessage) {
      super(source);
      Assert.isNotNull(source);
      Assert.isNotNull(settingsControl);
      this.settingsControl = settingsControl;
      this.newValue = newValue;
      this.validationMessage = validationMessage;
   }

   /**
    * Returns the changed setting control.
    * @return The changed setting control.
    */
   public ISettingControl getSettingsControl() {
      return settingsControl;
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
   public DataSourceSettingComposite getSource() {
      return (DataSourceSettingComposite)super.getSource();
   }
}