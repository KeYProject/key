/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.proof.runallproofs.proofcollection;

/**
 * Enum for properties, that .key-files can be tested on.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public enum TestProperty {
    PROVABLE, NOTPROVABLE, LOADABLE, NOTLOADABLE;
}
