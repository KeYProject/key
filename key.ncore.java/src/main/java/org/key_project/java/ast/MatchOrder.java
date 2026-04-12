package org.key_project.java.ast;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * This annotation allows you to define the order of matches calls on fields.
 *
 * @author Alexander Weigl
 * @version 1 (17.05.26)
 */
@Retention(RetentionPolicy.SOURCE)
@Target(ElementType.FIELD)
public @interface MatchOrder {
    int value() default 0;
}
