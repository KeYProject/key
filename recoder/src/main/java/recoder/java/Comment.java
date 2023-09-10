/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

/**
 * A comment, possibly with multiple lines.
 *
 * @author AL
 */

public class Comment extends JavaSourceElement {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 5919865992017191460L;

    /**
     * The text string.
     */

    protected String text;

    /**
     * Mark if the comment stands before its associated element.
     */

    protected boolean prefixed;
    /**
     * Parent.
     */

    protected ProgramElement parent;
    /**
     * Mark if the comment is the comment to a container; parser uses this only for empty containers
     * (i.e. StatementBlock, ArrayInitializer, ClassDeclaration)
     */
    private boolean isContainerComment;

    /**
     * Create a new empty comment. The comment contains an empty string, the slash-asterics markers
     * are not created.
     */

    public Comment() {
        text = "";
    }

    /**
     * Create a new comment with the given content. No extra comment markers are created.
     *
     * @param text the text of the comment.
     */

    public Comment(String text) {
        setText(text);
    }

    /**
     * Create a new comment with the given content. No extra comment markers are created.
     *
     * @param text the text of the comment.
     */

    public Comment(String text, boolean prefixed) {
        setText(text);
        setPrefixed(prefixed);
    }

    /**
     * Comment.
     *
     * @param proto a comment.
     */

    protected Comment(Comment proto) {
        super(proto);
        text = proto.text;
        prefixed = proto.prefixed;
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Comment deepClone() {
        return new Comment(this);
    }

    /**
     * Check if this comment should be prefixed in front of the parent element, or if it should
     * follow it.
     *
     * @return the boolean value.
     */

    public boolean isPrefixed() {
        return prefixed;
    }

    /**
     * Define if this comment should be prefixed in front of the parent element, or if it should
     * follow it. Implicitly sets isContainerComment to false.
     *
     * @param prefixed the boolean value.
     */

    public void setPrefixed(boolean prefixed) {
        this.prefixed = prefixed;
        this.isContainerComment = false;
    }

    public boolean isContainerComment() {
        return isContainerComment;
    }

    /**
     * Define if this comment should be a container comment. Implicitly sets isPrefixed to false.
     *
     * @param isContainerComment
     */
    public void setContainerComment(boolean isContainerComment) {
        this.isContainerComment = isContainerComment;
        this.prefixed = false;
    }

    /**
     * Get parent of the comment.
     *
     * @return the parent element.
     */

    public ProgramElement getParent() {
        return parent;
    }

    /**
     * Set parent of the comment.
     *
     * @param p a program element.
     */

    public void setParent(ProgramElement p) {
        parent = p;
    }

    /**
     * Get the comment text.
     *
     * @return the string with the complete content.
     */

    public String getText() {
        return text;
    }

    /**
     * Set text, including all markers. The text must contain all necessary leading and closing
     * tokens.
     *
     * @param text a string.
     */

    public void setText(String text) {
        this.text = text;
    }

    public void accept(SourceVisitor v) {
        v.visitComment(this);
    }
}
