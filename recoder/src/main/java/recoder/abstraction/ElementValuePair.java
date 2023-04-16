/*
 * Created on 10.06.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 *
 */
package recoder.abstraction;

/**
 * @author Tobias Gutzmann
 */
public interface ElementValuePair {
    /**
     * Returns the value. Can be either of
     * <ul>
     * <li>any boxed primitive type
     * <li>java.lang.String
     * <li>any subtype of java.lang.Class
     * <li>
     * <li>a one-dimensional array of any of the above.
     * </ul>
     *
     * @return
     */
    Object getValue();

    String getElementName();

    // String getFullNameOfContainingAnnotation();
}
