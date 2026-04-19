package org.key_project.java.ast;


import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/// Marks the ROOT class of the hierarchy
@Retention(RetentionPolicy.SOURCE)
@Target({ElementType.TYPE})
public @interface Root {
}
