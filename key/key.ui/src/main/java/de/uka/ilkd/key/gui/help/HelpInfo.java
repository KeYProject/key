package de.uka.ilkd.key.gui.help;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

/**
 * @author Alexander Weigl
 * @version 1 (10.04.19)
 */
@Retention(RetentionPolicy.RUNTIME)
public @interface HelpInfo {
    public String path() default "";
}
