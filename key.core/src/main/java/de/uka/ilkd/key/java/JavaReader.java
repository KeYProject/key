/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;


import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.IProgramVariable;

public interface JavaReader {

    JavaBlock readBlockWithEmptyContext(String s);

    JavaBlock readBlockWithProgramVariables(Namespace<IProgramVariable> varns, String s);

}
