/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.util;

/**
 * @author RN
 */
public class MissingOptionValueException extends OptionException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -2394702516972821831L;

    public MissingOptionValueException(String opt) {
        super(opt);
    }

    public String toString() {
        return "Missing value for option \"" + opt + "\"";
    }

}
