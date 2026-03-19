/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

public class SMTTranslationException extends Exception {

    /**
     *
     */
    private static final long serialVersionUID = -2230789489767950432L;

    public SMTTranslationException() {
    }

    public SMTTranslationException(String message) {
        super(message);
    }

    public SMTTranslationException(Throwable cause) {
        super(cause);
    }

    public SMTTranslationException(String message, Throwable cause) {
        super(message, cause);
    }

    public SMTTranslationException(String message, Throwable cause, boolean enableSuppression,
            boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }

}
