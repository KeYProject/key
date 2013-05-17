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

package de.hentschel.visualdbc.datasource.model;

import java.util.Map;

import org.eclipse.jface.viewers.ISelection;

/**
 * Represents a setting required to connect to a data source.
 * @author Martin Hentschel
 */
public interface IDSConnectionSetting {
   /**
    * The name of they key used in the {@link Map} in
    * {@link IDSConnection#connect(Map, boolean, org.eclipse.core.runtime.IProgressMonitor)}.
    * @return The name of the key.
    */
   public String getKey();
   
   /**
    * The human readable name that is displayed in the UI.
    * @return The human readable name.
    */
   public String getName();
   
   /**
    * <p>
    * The ID of the control that should be used to edit the value.
    * </p>
    * <p>
    * By default in Eclipse the control realizes the interfaces
    * {@code de.hentschel.visualdbc.datasource.ui.setting.ISettingControl}.
    * The control's implementation is registered via extension point 
    * {@code de.hentschel.visualdbc.datasource.ui.setting.util.SettingControlUtil#SETTING_CONTROL_EXTENSION_POINT}
    * </p>
    * @return The control ID.
    */
   public String getControlId();
   
   /**
    * Returns the initial value respecting the given {@link ISelection}.
    * @param selection The given {@link ISelection}.
    * @return The initial value.
    */
   public Object getInitialValue(ISelection selection);
}