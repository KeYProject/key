/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.inst;

import java.io.Serial;

/**
 * this exception is thrown from an "SVInstantiations"-Object if the sorts of a schema variable and
 * its instantiation are not compatible (and not generic)
 */
public class SortException extends IllegalInstantiationException {

    /**
     *
     */
    @Serial
    private static final long serialVersionUID = -1659749880755516351L;

    public SortException(String description) {
        super(description);
    }


}
