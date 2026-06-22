/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.scripts.meta.ProofScriptArgument;

/// Base class for proof script commands that do not accept any arguments.
/// Simplifies implementation by providing an empty argument list.
///
/// @author Alexander Weigl
/// @version 1 (28.03.17)
public abstract class NoArgumentCommand implements ProofScriptCommand {
    @Override
    public List<ProofScriptArgument> getArguments() {
        return new ArrayList<>();
    }
}
