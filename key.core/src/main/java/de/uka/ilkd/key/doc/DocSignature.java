/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.doc;

import java.util.List;

/**
 * One signature of a documented construct: its formal parameters and the documentation of the
 * signature itself. For variable conditions, multiple signatures describe the overloads of a
 * trigger name.
 *
 * @param parameters the formal parameters of the signature
 * @param documentation the documentation of this signature in markdown
 * @param negated whether the construct is also available negated (as {@code \not<name>}); only
 *        set for variable conditions
 *
 * @author Alexander Weigl
 * @version 1 (22.10.26)
 */
public record DocSignature(List<DocParameter> parameters, String documentation, boolean negated) {
}
