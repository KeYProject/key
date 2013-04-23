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

package org.key_project.monkey.product.ui.model;

import org.key_project.util.java.StringUtil;

/**
 * Represents the proof status of a {@link MonKeYProof}.
 * @author Martin Hentschel
 */
public enum MonKeYProofResult {
    /**
     * Proof was not tried.
     */
    UNKNOWN,
    
    /**
     * Proof is still open after automatic try.
     */
    OPEN,
    
    /**
     * Proof is fulfilled after automatic try.
     */
    CLOSED;
    
    /**
     * Returns a human readable text.
     * @return The human readable text.
     */
    public String getDisplayText() {
        switch (this) {
            case OPEN : return "Open";
            case CLOSED : return "Closed";
            default : return StringUtil.EMPTY_STRING;
        }
    }
}