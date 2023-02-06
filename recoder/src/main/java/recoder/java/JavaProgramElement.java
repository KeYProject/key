// This file is part of the RECODER library and protected by the LGPL.

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
            for (int i = 0; i < comments.size(); i++) {
                comments.get(i).setParent(this);
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
