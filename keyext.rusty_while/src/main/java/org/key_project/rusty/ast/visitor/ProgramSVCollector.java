/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.visitor;

import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.util.collection.ImmutableList;

public class ProgramSVCollector {
    /**
     * create the ProgramSVCollector
     *
     * @param root the ProgramElement where to begin
     * @param vars the IList<SchemaVariable> where to add the new-found ones
     * @param svInst the SVInstantiations previously found in order to determine the needed labels
     *        for the UnwindLoop construct.
     */
    public ProgramSVCollector(RustyProgramElement root, ImmutableList<SchemaVariable> vars,
            SVInstantiations svInst) {
        // super(root);
        // result = vars;
        // instantiations = svInst;
    }

    /** starts the walker */
    public void start() {

    }

    public ImmutableList<SchemaVariable> getSchemaVariables() {
        return null;
    }
}
