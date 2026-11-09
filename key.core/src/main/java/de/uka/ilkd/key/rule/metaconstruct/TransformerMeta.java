/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

/**
 * Meta data of a (program or term) transformer: its internal meta-construct name, i.e. the same
 * name that is passed to {@code super(...)} by the annotated transformer class. Used by
 * {@link de.uka.ilkd.key.doc.CodeTransformerDoc} to generate the transformer documentation.
 *
 * @author Alexander Weigl
 * @version 1 (22.10.26)
 */
@Retention(RetentionPolicy.RUNTIME)
public @interface TransformerMeta {
    String name();
}
