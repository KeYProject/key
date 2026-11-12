/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.help;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Annotate the help page for your component.
 * <p>
 * JavaFX port of {@code de.uka.ilkd.key.gui.help.HelpInfo} (Swing {@code HelpInfo.java:1-31}),
 * used by {@link HelpFacadeF} to resolve the documentation page of the focused component. The
 * Swing annotation is applied to {@code keyext.*} classes and to {@code MainWindow} ({@code
 * MainWindow.java:90}) — the FX main window is covered by {@link HelpFacadeF}'s main-page
 * fallback instead (see the port notes there).
 *
 * @see HelpFacadeF
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ ElementType.TYPE })
public @interface HelpInfoF {
    /**
     * The relative part of the URL to the {@link HelpFacadeF#HELP_BASE_URL}.
     * <p>
     * May also be an absolute URL starting with {@code https://}.
     * </p>
     *
     * @return non-null string
     */
    String path() default "";
}
