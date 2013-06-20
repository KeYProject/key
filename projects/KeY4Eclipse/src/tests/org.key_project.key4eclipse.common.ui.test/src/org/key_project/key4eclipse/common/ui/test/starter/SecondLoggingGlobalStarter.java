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

import org.key_project.key4eclipse.common.ui.starter.IGlobalStarter;

/**
 * {@link IGlobalStarter} which logs the calls of {@link #open()}.
 * @author Martin Hentschel
 */
public class SecondLoggingGlobalStarter implements IGlobalStarter, ITestedStarter {
   /**
    * The unique ID of this starter.
    */
   public static final String ID = "org.key_project.key4eclipse.common.ui.test.starter.SecondLoggingGlobalStarterID";

   /**
    * The unique Name of this starter.
    */
   public static final String NAME = "Second Global Starter";

   /**
    * The description of this starter.
    */
   public static final String DESCRIPTION = "Description of Second Global Starter";

   /**
    * The counted number of calls.
    */
   private int openCount = 0;

   /**
    * {@inheritDoc}
    */
   @Override
   public void open() throws Exception {
      openCount++;
   }
   
   /**
    * Returns the counted number of calls and resets it to zero.
    * @return The number of calls.
    */
   public int getAndResetOpenCount() {
      int result = openCount;
      openCount = 0;
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getId() {
      return ID;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return NAME;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getDescription() {
      return DESCRIPTION;
   }
}