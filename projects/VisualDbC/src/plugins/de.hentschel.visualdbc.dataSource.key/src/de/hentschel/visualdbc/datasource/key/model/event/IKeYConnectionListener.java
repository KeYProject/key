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

package de.hentschel.visualdbc.datasource.key.model.event;

import java.util.EventListener;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.key.model.KeyProof;

/**
 * Allows to observe changes on a {@link KeyConnection}.
 * @author Martin Hentschel
 */
public interface IKeYConnectionListener extends EventListener {
   /**
    * When an interactive {@link KeyProof} was started.
    * @param e The {@link KeYConnectionEvent}.
    */
   public void interactiveProofStarted(KeYConnectionEvent e);
}