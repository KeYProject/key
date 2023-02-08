/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

/**
 * Strict fp.
 *
 * @author <TT>AutoDoc</TT>
 */

public class StrictFp extends Modifier {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 6903473464189070008L;

    /**
     * Strict fp.
     */

    public StrictFp() {
        // nothing to do
    }

    /**
     * Strict fp.
     *
     * @param proto a strict fp.
     */

    protected StrictFp(StrictFp proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public StrictFp deepClone() {
        return new StrictFp(this);
    }

    public void accept(SourceVisitor v) {
        v.visitStrictFp(this);
    }

}
