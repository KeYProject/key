/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.visitor;

import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * This visitor is used to collect all appearing SchemaVariables in a java program
 */
public class ProgramSVCollector extends RustyASTWalker {
    private ImmutableList<SchemaVariable> result = ImmutableSLList.nil();

    /** the instantiations needed for unwind loop constructs */
    private SVInstantiations instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;

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
        super(root);
        result = vars;
        instantiations = svInst;
    }

    /** starts the walker */
    public void start() {
        walk(root());
    }

    public ImmutableList<SchemaVariable> getSchemaVariables() {
        return result;
    }

    /**
     * the action that is performed just before leaving the node the last time. Not only schema
     * variables must be taken into consideration, but also program meta constructs with implicit
     * schema variables containment
     *
     */
    @Override
    protected void doAction(RustyProgramElement node) {
        if (node instanceof SchemaVariable) {
            result = result.prepend((SchemaVariable) node);
        }
    }
}
