/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.logic.Name;

/**
 * The axiom command takes one argument: a formula to which the command is applied.
 *
 * @see AssumeCommand The assume command is a synonym for the axiom command.
 *
 * @Deprecated This command is deprecated and should not be used in new scripts. It is kept for compatibility reasons.
 * Use the {@link AssumeCommand} "assume" instead.
 */
public class AxiomCommand extends AssumeCommand {

    @Override
    public String getName() {
        return "axiom";
    }
}