/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

import recoder.ModelException;
import recoder.list.generic.ASTList;

/**
 * Top level implementation of a Java {@link ProgramElement}.
 *
 * @author AL
 */

public abstract class JavaProgramElement extends JavaSourceElement implements ProgramElement {

    /**
     * Comments.
     */

    protected ASTList<Comment> comments;

    /**
     * Java program element.
     */

    public JavaProgramElement() {
        // nothing to do here
    }

    /**
     * Java program element.
     *
     * @param proto a java program element.
     */

    protected JavaProgramElement(JavaProgramElement proto) {
        super(proto);
        if (proto.comments != null) {
            comments = proto.comments.deepClone();
        }
    }

    /**
     * Get comments.
     *
     * @return the comments.
     */

    public ASTList<Comment> getComments() {
        return comments;
    }

    /**
     * Set comments.
     *
     * @param c a comment list.
     */

    public void setComments(ASTList<Comment> list) {
        comments = list;
        if (comments != null) {
            for (Comment comment : comments) {
                comment.setParent(this);
            }
        }
    }

    /**
     * Defaults to do nothing.
     */

    public void validate() throws ModelException {
        /* Defaults to do nothing. */
    }
}
