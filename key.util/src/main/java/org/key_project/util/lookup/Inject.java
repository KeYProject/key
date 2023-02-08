package org.key_project.util.lookup;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

/**
 * Marker annotations for setters or constructors to inject implementations.
 *
 * @author Alexander Weigl
 * @version 1 (13.01.19)
 *
 * @see Lookup#createInstance(Class)
 * @see Lookup#inject(Object)
 */
@Retention(RetentionPolicy.RUNTIME)
public @interface Inject {
}
