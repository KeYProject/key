// This file is part of the RECODER library and protected by the LGPL.

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
        StringBuffer res = new StringBuffer();
        for (int i = 0; i < changeList.size(); i += 1) {
            res.append(changeList.get(i).toString());
            res.append("\n");
        }
        return res.toString();
    }
}
