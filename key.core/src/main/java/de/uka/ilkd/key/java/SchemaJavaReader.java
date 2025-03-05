/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import org.key_project.logic.Namespace;
import org.key_project.logic.op.sv.SchemaVariable;

public interface SchemaJavaReader extends JavaReader {

    void setSVNamespace(Namespace<SchemaVariable> ns);
}
