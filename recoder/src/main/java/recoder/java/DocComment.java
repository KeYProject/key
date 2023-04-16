// This file is part of the RECODER library and protected by the LGPL.

package recoder.java;

/**
 * Contains tags with
 *
 * @-prefix and corresponding entries.
 */

public class DocComment extends Comment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 621277739856803262L;

    /**
     * Doc comment.
     */

    public DocComment() {
        super();
        setPrefixed(true);
    }

    /**
     * Doc comment.
     *
     * @param text a string.
     */

    public DocComment(String text) {
        super(text, true);
    }

    /**
     * Doc comment.
     *
     * @param proto a doc comment.
     */

    protected DocComment(DocComment proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public DocComment deepClone() {
        return new DocComment(this);
    }

    public void accept(SourceVisitor v) {
        v.visitDocComment(this);
    }

}
