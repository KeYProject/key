/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit.pattern;

import recoder.ModelException;

public class InconsistentPatternException extends ModelException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 1L;

    public InconsistentPatternException() {
        super();
    }

    public InconsistentPatternException(String s) {
        super(s);
    }
}
