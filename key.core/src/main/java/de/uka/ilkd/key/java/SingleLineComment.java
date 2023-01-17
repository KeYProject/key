package de.uka.ilkd.key.java;

/** Any non-SingleLineComment is a multi line comment. */

public class SingleLineComment extends Comment {

    /**
     * Single line comment.
     */

    public SingleLineComment() {}

    /**
     * Single line comment.
     *
     * @param text a string.
     */

    public SingleLineComment(String text) {
        super(text);
    }
}
