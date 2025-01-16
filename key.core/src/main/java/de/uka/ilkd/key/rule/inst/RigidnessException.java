/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.inst;

import java.io.Serial;

import org.key_project.prover.rules.instantiation.IllegalInstantiationException;

/**
 * this exception is thrown if non-rigid instantiation has been given for a schema variable only
 * allowing rigid instantiations
 */
public class RigidnessException extends IllegalInstantiationException {

    /**
     *
     */
    @Serial
    private static final long serialVersionUID = 1109354128591892703L;

    public RigidnessException(String description) {
        super(description);
    }

}
