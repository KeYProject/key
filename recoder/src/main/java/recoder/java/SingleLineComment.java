/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

/**
 * Any non-SingleLineComment is a multi line comment.
 */

public class SingleLineComment extends Comment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -1462907890949586507L;

    /**
     * Single line comment.
     */

    public SingleLineComment() {
        // nothing to do here
    }

    /**
     * Single line comment.
     *
     * @param text a string.
     */

    public SingleLineComment(String text) {
        super(text);
    }

    /**
     * Single line comment.
     *
     * @param proto a single line comment.
     */

    protected SingleLineComment(SingleLineComment proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public SingleLineComment deepClone() {
        return new SingleLineComment(this);
    }

    public void accept(SourceVisitor v) {
        v.visitSingleLineComment(this);
    }

}
