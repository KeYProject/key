package de.uka.ilkd.key.nui.controller;

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
public @interface ControllerAnnotation {
    /**
     * Decides whether a menu entry in the 'View' menu should be created for the
     * View associated with this controller.
     * 
     * @return boolean indicating if the menu entry should be created.
     */
    boolean createMenu();
}
