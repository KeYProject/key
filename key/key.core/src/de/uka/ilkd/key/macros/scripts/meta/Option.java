package de.uka.ilkd.key.macros.scripts.meta;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * @author <TT>Unknown</TT>
 */
@Target(ElementType.FIELD) @Retention(RetentionPolicy.RUNTIME)
public @interface Option {
    String value();
    boolean required() default true;
}
