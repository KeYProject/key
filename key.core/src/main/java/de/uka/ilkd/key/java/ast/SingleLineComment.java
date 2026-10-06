/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast;


/** Any non-SingleLineComment is a multi line comment. */

public class SingleLineComment extends Comment {

    /**
     * Single line comment.
     */

    public SingleLineComment() {}

    /**
     * Single line comment.
     *
     * @param text
     *        a string.
     */

    public SingleLineComment(String text) {
        super(text);
    }
}
