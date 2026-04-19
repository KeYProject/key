package org.key_project.java.ast;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/// Sets the suffix of the package with respect to `org.key_project.java.ast`
@Retention(RetentionPolicy.SOURCE)
@Target({ElementType.TYPE})
public @interface Package {
    String value() default "";
}
