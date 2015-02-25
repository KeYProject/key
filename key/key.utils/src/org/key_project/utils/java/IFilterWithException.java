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

package org.key_project.util.java;

/**
 * Utility class to select elements which also allows that exceptions
 * are thrown during selection phase.
 * @author Martin Hentschel
 */
public interface IFilterWithException<T, E extends Throwable> {
    /**
     * Checks if the given element should be selected.
     * @param element The element to test.
     * @return {@code true} handle element, {@code false} ignore element.
     * @throws E An occurred exception.
     */
    public boolean select(T element) throws E;
}