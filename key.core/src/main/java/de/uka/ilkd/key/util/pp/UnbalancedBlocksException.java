/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.pp;

public class UnbalancedBlocksException extends IllegalStateException {
    /**
     *
     */
    private static final long serialVersionUID = 6975429107613832601L;

    public UnbalancedBlocksException() {
        super();
    }

    public UnbalancedBlocksException(String s) {
        super(s);
    }
}
