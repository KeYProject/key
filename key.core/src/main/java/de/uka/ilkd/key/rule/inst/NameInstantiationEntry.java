/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.inst;

import org.key_project.logic.Name;

/**
 * This class is used to store the instantiation of a schemavarible if it is a name.
 */
public class NameInstantiationEntry extends InstantiationEntry<Name> {

    NameInstantiationEntry(Name name) {
        super(name);
    }
}
