/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL

package recoder.util;

/**
 * @author RN
 */
public class UnknownOptionException extends OptionException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -5505614786119000814L;

    public UnknownOptionException(String opt) {
        super(opt);
    }

    public String toString() {
        return "Unknown option \"" + opt + "\"";
    }

}
