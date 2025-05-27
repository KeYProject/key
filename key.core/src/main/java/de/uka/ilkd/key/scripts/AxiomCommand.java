/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;


/**
 * The axiom command takes one argument: a formula to which the command is applied.
 *
 * @see AssumeCommand The assume command is a synonym for the axiom command.
 *
 * @deprecated This command is deprecated and should not be used in new scripts. It is kept for
 *             compatibility reasons.
 *             Use the {@link AssumeCommand} "assume" instead.
 */
@Deprecated(forRemoval = true)
public class AxiomCommand extends AssumeCommand {
    @Override
    public String getName() {
        return "axiom";
    }
}
