/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL

package recoder.util;

/**
 * @author RN
 */
public abstract class OptionException extends Exception {

    protected String opt;

    protected OptionException(String opt) {
        this.opt = opt;
    }

    public abstract String toString();

}
