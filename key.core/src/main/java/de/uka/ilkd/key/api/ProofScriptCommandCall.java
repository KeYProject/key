/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.api;

import de.uka.ilkd.key.macros.scripts.ProofScriptCommand;

/**
 * @param <T>
 * @author Alexander Weigl
 */
public class ProofScriptCommandCall<T> {
    final T parameter;
    final ProofScriptCommand<T> command;

    public ProofScriptCommandCall(ProofScriptCommand<T> command, T arguments) {
        parameter = arguments;
        this.command = command;
    }
}
