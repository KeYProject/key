/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL.

package recoder.kit;

import recoder.abstraction.Method;

/**
 * Problem report indicating that a method has been overwritten with a different return type.
 */
public class DifferentReturnTypeOverwrite extends Conflict {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 1569165840299545025L;
    private final Method method;

    public DifferentReturnTypeOverwrite(Method method) {
        this.method = method;
    }

    public Method getMethod() {
        return method;
    }
}
