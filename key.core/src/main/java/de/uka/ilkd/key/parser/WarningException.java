/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

public class WarningException extends antlr.ANTLRException {

    /**
     *
     */
    private static final long serialVersionUID = 3421160418830554998L;
    private String errorStr = "";

    public WarningException(String errorStr) {
        this.errorStr = errorStr;
    }

    public String getMessage() {
        return errorStr;
    }


    public String toString() {
        return errorStr;
    }

}
