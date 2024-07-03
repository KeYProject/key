/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import de.uka.ilkd.key.logic.op.SchemaVariable;

import org.key_project.logic.Namespace;

public interface SchemaJavaReader extends JavaReader {

    void setSVNamespace(Namespace<SchemaVariable> ns);
}
