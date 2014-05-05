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