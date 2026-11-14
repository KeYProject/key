/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.util.concurrent.Callable;

import picocli.CommandLine.Command;

/**
 * Stub for the {@code prove} subcommand.
 * <p>
 * Phase 1 placeholder: accepts the positional file arguments and the {@code --timeout} option so
 * that {@code key-cli prove ...} runs. The actual prove pipeline is implemented together with
 * {@code HeadlessProver} (Task 1.3).
 */
@Command(name = "prove", description = "Prove the contracts of the given KeY problem file(s).",
    mixinStandardHelpOptions = true)
public final class ProveCommand implements Callable<Integer> {

    @Override
    public Integer call() {
        return 0;
    }
}
