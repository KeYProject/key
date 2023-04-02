// This file is part of the RECODER library and protected by the LGPL.

package recoder.convenience;

/**
 * Default formatting strings that are useful for error reporting.
 *
 * @author AL
 */
public interface Formats {

    /**
     * Long default formatting string for program elements, handsome for descriptive external error
     * messages. Derives messages such as <TT>
     * MethodReference "x.f(i + 1)"
     *
     * &#64;23/45 in FILE:/tmp/Foo.java</TT>.
     */
    String ELEMENT_LONG = "%c \"%s\" @%p in %f";

    /**
     * Long formatting string for program elements, omitting file information. Derives messages such
     * as <TT>MethodReference "x.f(i + 1)"
     *
     * &#64;23/45</TT>.
     */
    String ELEMENT_LONG_LOCAL = "%c \"%s\" @%p";

    /**
     * Short default formatting string for named program elements, handsome for descriptive external
     * error messages. Derives messages such as <TT>
     * MethodDeclaration "Foo.f(int)"
     *
     * &#64;23/45 in FILE:/tmp/Foo.java</TT>.
     */
    String ELEMENT_SHORT = "%c \"%N\" @%p in %f";
}
