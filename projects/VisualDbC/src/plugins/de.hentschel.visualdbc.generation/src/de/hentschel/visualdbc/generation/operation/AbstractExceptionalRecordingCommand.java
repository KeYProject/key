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

package de.hentschel.visualdbc.generation.operation;

import org.eclipse.emf.transaction.RecordingCommand;
import org.eclipse.emf.transaction.TransactionalEditingDomain;

/**
 * A basic implementation of {@link RecordingCommand} that handles occurred 
 * {@link Exception}s in {@link #doExecute()} by saving them in the instance
 * variable {@link #exception}. 
 * @author Martin Hentschel
 */
public abstract class AbstractExceptionalRecordingCommand<T extends Exception> extends RecordingCommand {
   /**
    * The caught exception.
    */
   private T exception;

   /**
    * Constructor.
    * @param domain The domain.
    * @param label The label.
    * @param description The description.
    */
   public AbstractExceptionalRecordingCommand(TransactionalEditingDomain domain, String label, String description) {
      super(domain, label, description);
   }

   /**
    * Constructor.
    * @param domain The domain.
    * @param label The label.
    */
   public AbstractExceptionalRecordingCommand(TransactionalEditingDomain domain, String label) {
      super(domain, label);
   }

   /**
    * Constructor.
    * @param domain The domain.
    */
   public AbstractExceptionalRecordingCommand(TransactionalEditingDomain domain) {
      super(domain);
   }

   /**
    * Returns the caught exception.
    * @return The caught exception.
    */
   public T getException() {
      return exception;
   }

   /**
    * Sets the caught exception.
    * @param exception The caught exception.
    */
   protected void setException(T exception) {
      this.exception = exception;
   }
}