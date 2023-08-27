/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.inst;

/**
 * This exception thrown if there is no appropriate instantiation of the generic sorts occurring
 * within an "SVInstantiations"-object
 */
import org.key_project.util.collection.ImmutableList;

/**
 * This exception thrown if there is no appropriate instantiation of the generic sorts occurring
 * within an "SVInstantiations"-object
 */
public class GenericSortException extends SortException {

    /**
     *
     */
    private static final long serialVersionUID = 1372231759025588273L;

    private ImmutableList<GenericSortCondition> conditions;

    public GenericSortException(String description,
            ImmutableList<GenericSortCondition> pConditions) {
        super(description);
        this.conditions = pConditions;
    }

    public GenericSortException(String description) {
        super(description);
    }

    public void setConditions(ImmutableList<GenericSortCondition> pConditions) {
        this.conditions = pConditions;
    }

    public String getMessage() {
        return super.getMessage() + (conditions == null ? "" : conditions);
    }
}
