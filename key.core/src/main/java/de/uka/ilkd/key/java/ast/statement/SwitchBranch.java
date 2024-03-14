/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.PositionInfo;

import org.key_project.util.ExtList;

public abstract class SwitchBranch extends BranchImp {
    public SwitchBranch() {
        super();
    }

    public SwitchBranch(ExtList children) {
        super(children);
    }

    public SwitchBranch(ExtList children, PositionInfo pos) {
        super(children, pos);
    }
}
