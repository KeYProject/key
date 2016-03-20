package de.uka.ilkd.key.nui.prooftree.filter;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Used for annotation of controllers with specific properties.
 *
 * @author Florian Breitfelder
 *
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
public @interface FilterAnnotation {

    /**
     * Decides whether the class is a filter and should be loaded by reflection
     * during runtime, see {@link FilteringHandler#searchFilterClasses()}.
     * 
     * @return a boolean indicating whether the file is an filter to be loaded
     *         during runtime.
     */
    boolean isFilter();

}
