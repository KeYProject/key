/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

/**
 * Exception thrown by the change history in case of illegal change reports.
 */
public class IllegalChangeReportException extends RuntimeException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 1930002520114622048L;

    /**
     * Creates a new illegal change report exception.
     */
    public IllegalChangeReportException() {
        super();
    }

    /**
     * Creates a new illegal change report exception.
     *
     * @param msg a string.
     */
    public IllegalChangeReportException(String msg) {
        super(msg);
    }
}
