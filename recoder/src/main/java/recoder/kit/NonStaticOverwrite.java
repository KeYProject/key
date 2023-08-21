/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

import recoder.abstraction.Method;

/**
 * Problem report indicating that a static method has been overwritten with a non-static version.
 */
public class NonStaticOverwrite extends Conflict {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -3618890938924075301L;
    private final Method method;

    public NonStaticOverwrite(Method method) {
        this.method = method;
    }

    public Method getMethod() {
        return method;
    }
}
