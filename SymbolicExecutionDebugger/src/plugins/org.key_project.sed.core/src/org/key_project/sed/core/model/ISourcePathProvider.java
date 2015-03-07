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

package org.key_project.sed.core.model;

/**
 * Classes that implements this interface provides the path of a file
 * that is treated, edited or what else.
 * @author Martin Hentschel
 */
public interface ISourcePathProvider {
   /**
    * Returns the source path.
    * @return The source path.
    */
   public String getSourcePath();
}