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

package org.key_project.key4eclipse.common.ui.test.starter;

/**
 * Defines the common functionality to tes starter.
 * @author Martin Hentschel
 */
public interface ITestedStarter {
   /**
    * Returns The unique ID.
    * @return The unique ID.
    */
   public String getId();
   
   /**
    * Returns the name.
    * @return The name.
    */
   public String getName();
   
   /**
    * Returns the description.
    * @return The description.
    */
   public String getDescription();
}