/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.doc;

import java.util.List;

import org.jspecify.annotations.Nullable;

/**
 * One documented construct of the taclet language, e.g. a variable condition, a proof script
 * command, or a code transformer. The record doubles as the JSON schema of the documentation dump:
 * the generators build a {@code List<DocItem>} which is serialized verbatim and from which the
 * markdown document is rendered.
 *
 * @param name the trigger name of the construct (e.g. {@code \find}, {@code \select}, or the
 *        transformer meta-construct name)
 * @param documentation the general documentation of the construct in markdown
 * @param signatures the signatures (overloads, constructors, or argument lists) of the construct
 * @param category the category of the construct, only set for proof script commands
 * @param deprecated whether the construct is deprecated, only set for proof script commands
 *
 * @author Alexander Weigl
 * @version 1 (22.10.26)
 */
public record DocItem(String name, String documentation, List<DocSignature> signatures,
        @Nullable String category, boolean deprecated) {
}
