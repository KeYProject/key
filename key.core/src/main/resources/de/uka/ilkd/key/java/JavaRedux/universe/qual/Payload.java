package universe.qual;


import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * The Payload modifier expresses that the underlying object cannot be accessed in any way.
 *
 * @author Daniel Grévent
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_PARAMETER, ElementType.TYPE_USE})
public @interface Payload {}
