/*
 * Created on 25.05.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 *
 */
package recoder.abstraction;


/**
 * @author gutzmann
 *         <p>
 *         a program model element representing annotation properties.
 */
public interface AnnotationProperty extends Method {
    /**
     * Returns the default value for the annotation member represented by this Method instance.
     * Returns null if no default is associated with the member, or if the method instance does not
     * represent a declared member of an annotation type.
     *
     * @return the default value for the annotation member represented by this Method instance.
     */
    Object getDefaultValue();
}
