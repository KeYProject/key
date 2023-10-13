/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

/**
 * Jump statement.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class JumpStatement extends JavaStatement {

    /**
     * Jump statement.
     */

    public JumpStatement() {
        // nothing to do
    }

    /**
     * Jump statement.
     *
     * @param proto a jump statement.
     */

    protected JumpStatement(JumpStatement proto) {
        super(proto);
    }
}
