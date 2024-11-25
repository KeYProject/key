/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.util;

/** this exception is shown if an assertion has failed */
public class AssertionFailure extends RuntimeException {
    /**
     *
     */
    private static final long serialVersionUID = -235001842777133987L;

    public AssertionFailure() {
        super();
    }

    public AssertionFailure(String msg) {
        super(msg);
    }
}
