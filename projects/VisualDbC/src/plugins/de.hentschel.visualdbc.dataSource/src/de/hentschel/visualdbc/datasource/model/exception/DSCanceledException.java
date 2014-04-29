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

package de.hentschel.visualdbc.datasource.model.exception;

/**
 * This exception is thrown if a progress in a data source was canceled.
 * @author Martin Hentschel
 */
public class DSCanceledException extends Exception {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = -4174126161134481692L;

   /**
    * Constructor.
    */
   public DSCanceledException() {
   }
}