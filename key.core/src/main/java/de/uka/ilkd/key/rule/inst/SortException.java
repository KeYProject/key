/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.inst;

import org.key_project.prover.rules.instantiation.IllegalInstantiationException;

/**
 * this exception is thrown from an "SVInstantiations"-Object if the sorts of a schema variable and
 * its instantiation are not compatible (and not generic)
 */
public class SortException extends IllegalInstantiationException {

    /**
     *
     */
    private static final long serialVersionUID = -1659749880755516351L;

    public SortException(String description) {
        super(description);
    }


}
