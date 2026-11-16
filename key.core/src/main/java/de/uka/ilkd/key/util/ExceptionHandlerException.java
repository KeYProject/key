/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.util;


import java.util.Objects;

import org.jspecify.annotations.NullMarked;

/** This Exception is only thrown by the ExceptionHandler */

@NullMarked
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
        // All constructors guarantee a non-null message (the Throwable one stores
        // cause.toString()).
        return Objects.requireNonNull(super.getMessage(), "exception message");
    }
}
