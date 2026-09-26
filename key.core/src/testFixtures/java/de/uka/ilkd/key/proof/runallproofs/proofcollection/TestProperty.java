/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.runallproofs.proofcollection;

/**
 * Enum for properties, that .key-files can be tested on.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public enum TestProperty {
    PROVABLE, NOTPROVABLE, LOADABLE, NOTLOADABLE
}
