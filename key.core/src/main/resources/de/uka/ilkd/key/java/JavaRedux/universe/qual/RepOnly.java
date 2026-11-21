package universe.qual;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * The RepOnly modifier expresses that a method can only access owned fields and other RepOnly
 * methods.
 *
 * @author Daniel Grévent
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
public @interface RepOnly {}
