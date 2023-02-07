/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL

package recoder.util;

/**
 * @author RN
 */
public class OptionMultiplicityException extends OptionException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 1892377246432205468L;

    public OptionMultiplicityException(String opt) {
        super(opt);
    }

    public String toString() {
        return "Option \"" + opt + "\" does not allow multiple values";
    }

}
