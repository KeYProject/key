/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.doc;

import org.jspecify.annotations.Nullable;

/**
 * A formal parameter of a documented construct's signature.
 *
 * @param name the name of the parameter
 * @param type the canonical type name of the parameter, or {@code null} for parameters that
 *        only contribute documentation (e.g. javadoc parameters beyond the declared arguments)
 * @param description the documentation of the parameter in markdown, or {@code null}
 * @param kind the kind of the argument (flag, option, or positional); only set for proof script
 *        commands
 * @param required whether the argument is mandatory; only set for proof script commands
 * @param position the position of a positional argument; only set for positional arguments of
 *        proof script commands
 * @param varargs whether the argument accepts a variable number of values; only set for proof
 *        script commands
 *
 * @author Alexander Weigl
 * @version 1 (22.10.26)
 */
public record DocParameter(String name, @Nullable String type, @Nullable String description,
        @Nullable String kind, boolean required, @Nullable Integer position, boolean varargs) {
}
