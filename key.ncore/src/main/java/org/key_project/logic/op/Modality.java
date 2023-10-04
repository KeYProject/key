/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;

/**
 * This class is used to represent a dynamic logic modality like diamond and box for a target
 * language.
 */
public abstract class Modality extends AbstractSortedOperator {
    /**
     * Whether this modality is termination sensitive, i.e., it is a "diamond-kind" modality.
     */
    private final boolean isTerminationSensitive;

    /**
     * Whether this is a transaction modality.
     */
    private final boolean isTransaction;

    protected Modality(Name name, Sort formulaSort, boolean isTerminationSensitive, boolean isTransaction) {
        super(name, new Sort[] { formulaSort }, formulaSort, false);
        this.isTerminationSensitive = isTerminationSensitive;
        this.isTransaction = isTransaction;
    }

    public boolean terminationSensitive() {
        return isTerminationSensitive;
    }

    public boolean transaction() {
        return isTransaction;
    }
}
