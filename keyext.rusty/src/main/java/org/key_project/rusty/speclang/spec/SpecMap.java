/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang.spec;

import org.key_project.rusty.parser.hir.DefId;
import org.key_project.rusty.parser.hir.HirId;

public record SpecMap(Entry<DefId, FnSpec>[] fnSpecs, Entry<HirId, LoopSpec>[] loopSpecs) {
}
