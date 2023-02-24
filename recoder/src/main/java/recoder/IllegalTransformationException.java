/**
 * This file is part of the RECODER library and protected by the LGPL. created on 04.12.2007
 */
package recoder;

/**
 * An exception indicating that a transformation performed on the abstract syntax tree leaves the
 * internal datastructures in an inconsistent state. This transformation is a &quot;workaround&quot;
 * for some known bugs. Currently, the exception is thrown only for one reason: When exchanging an
 * Identifier which is contained in a PackageSpecification. A workaround is to exchange either the
 * containing PackageReference or the containing PackageSpecification.
 *
 * @author Tobias Gutzmann
 */
public class IllegalTransformationException extends RuntimeException {
    /**
     *
     */
    public IllegalTransformationException() {
        // standard constructor
    }

    /**
     * @param message
     */
    public IllegalTransformationException(String message) {
        super(message);
    }
}
