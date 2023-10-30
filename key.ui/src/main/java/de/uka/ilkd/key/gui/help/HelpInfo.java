/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.help;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * @author Alexander Weigl
 * @version 1 (10.04.19)
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ ElementType.TYPE })
/**
 * Annotate the help page for your component.
 *
 * @see HelpFacade
 */
public @interface HelpInfo {
    /**
     * The relative part of the URL to the {@link HelpFacade#HELP_BASE_URL}.
     *
     * @return non-null string
     */
    String path() default "";
}
