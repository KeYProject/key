/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.util;

/**
 * @author RN
 */
public class MissingArgumentException extends OptionException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -202835350467537194L;

    public MissingArgumentException(String opt) {
        super(opt);
    }

    public String toString() {
        return "Missing mandatory argument \"" + opt + "\"";
    }

}
