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

package de.hentschel.visualdbc.datasource.model.memory;

import de.hentschel.visualdbc.datasource.model.DSVisibility;
import de.hentschel.visualdbc.datasource.model.IDSConstructor;

/**
 * Default implementation for an {@link IDSConstructor} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryConstructor extends MemoryOperation implements IDSConstructor {
   /**
    * Default constructor.
    */
   public MemoryConstructor() {
      super();
   }
   
   /**
    * Constructor.
    * @param signature The constructor signature.
    * @param visibility The visibility.
    */
   public MemoryConstructor(String signature, DSVisibility visibility) {
      super(signature, visibility);
   }
}