/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import java.util.List;

/**
 * Record of the syntactical changes that occured after the last validation of the model.
 *
 * @author AL
 * @since 0.5
 */
public class ChangeHistoryEvent extends java.util.EventObject {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -5303809748311641541L;
    private final List<TreeChange> changeList;

    ChangeHistoryEvent(ChangeHistory source, List<TreeChange> changeList) {
        super(source);
        this.changeList = changeList;
    }

    /**
     * Returns the series of changes.
     */
    public List<TreeChange> getChanges() {
        return changeList;
    }

    public String toString() {
        StringBuilder res = new StringBuilder();
        for (TreeChange treeChange : changeList) {
            res.append(treeChange.toString());
            res.append("\n");
        }
        return res.toString();
    }
}
