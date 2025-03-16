/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.parser.Location;

import org.jspecify.annotations.NonNull;

/**
 * This struct encapsulate the information of a proofscript found in key files.
 *
 * @param script the content of the script
 * @param location location of the content
 * @author Alexander Weigl
 * @version 1 (23.04.24)
 */
public record ProofScriptEntry(@NonNull String script, @NonNull Location location) {
}
