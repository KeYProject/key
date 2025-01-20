/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
