/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.util;

/**
 * @author RN
 */
public class IllegalOptionValueException extends OptionException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 3501805964861992020L;
    final String val;

    public IllegalOptionValueException(String opt, String val) {
        super(opt);
        this.val = val;
    }

    public String toString() {
        return "Illegal value \"" + val + "\" for option \"" + opt + "\"";
    }

}
