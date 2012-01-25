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

package de.hentschel.visualdbc.datasource.ui.composite.event;

import java.util.EventListener;

import de.hentschel.visualdbc.datasource.ui.composite.DataSourceSettingComposite;

/**
 * Listens for changes on a {@link DataSourceSettingComposite}.
 * @author Martin Hentschel
 */
public interface IDataSourceSettingCompositeListener extends EventListener {
   /**
    * When a value of a setting has changed.
    * @param e The event.
    */
   public void settingValueChanged(DataSourceSettingCompositeEvent e);
}
