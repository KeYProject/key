/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

public abstract class SwitchBranch extends Branch {

    public SwitchBranch() {
        super();
    }

    /**
     * Branch.
     *
     * @param proto a branch.
     */

    protected SwitchBranch(SwitchBranch proto) {
        super(proto);
    }

    @Override
    public Switch getParent() {
        return (Switch) parent;
    }

    /**
     * Set parent.
     *
     * @param parent a switch.
     */

    public void setParent(Switch parent) {
        this.parent = parent;
    }
}
