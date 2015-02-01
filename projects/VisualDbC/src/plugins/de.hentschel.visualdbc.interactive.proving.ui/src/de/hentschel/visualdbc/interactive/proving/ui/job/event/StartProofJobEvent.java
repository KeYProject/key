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

package de.hentschel.visualdbc.interactive.proving.ui.job.event;

import java.util.EventObject;

import de.hentschel.visualdbc.interactive.proving.ui.job.StartProofJob;

/**
 * An event thrown from a {@link StartProofJob} and observed via
 * {@link IStartProofJobListener}.
 * @author Martin Hentschel
 */
public class StartProofJobEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = -2591196704008024760L;

   /**
    * Constructor.
    * @param source The {@link StartProofJob} that has thrown this event.
    */
   public StartProofJobEvent(StartProofJob source) {
      super(source);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public StartProofJob getSource() {
      return (StartProofJob)super.getSource();
   }
}