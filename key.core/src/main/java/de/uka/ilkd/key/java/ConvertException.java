/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

/**
 * This exception class is mainly thrown by Recoder2KeY and its companions.
 *
 * It stores its reason not only by the cause mechanism of Exceptions but also separately if it is a
 * parser error.
 *
 * This information is then read by the KeYParser to produce helpful error messages.
 *
 */
public class ConvertException extends RuntimeException {
    public ConvertException(String message) {
        super(message);
    }
}
