/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.util;


/** This Exception is only thrown by the ExceptionHandler */

public class ExceptionHandlerException extends RuntimeException {

    /**
     *
     */
    private static final long serialVersionUID = 4804191909840321109L;

    public ExceptionHandlerException() {
        super("An Exception occurred");
    }

    public ExceptionHandlerException(String msg) {
        super(msg);
    }

    public ExceptionHandlerException(Throwable ex) {
        super(ex);
    }

    @Override
    public String getMessage() {
        return toString();
    }

    @Override
    public String toString() {
        return super.getMessage();
    }
}
