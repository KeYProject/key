/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.util.HashSet;
import java.util.LinkedHashSet;

import org.key_project.logic.Term;
import org.key_project.logic.Visitor;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.visitor.ProgramVariableCollector;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.ProgramVariable;

import org.jspecify.annotations.NonNull;

public class TermProgramVariableCollector implements Visitor<@NonNull Term> {

    private final HashSet<ProgramVariable> result = new LinkedHashSet<>();
    private final Services services;


    public TermProgramVariableCollector(Services services) {
        this.services = services;
    }

    /**
     * is called by the execPostOrder-method of a term
     *
     * @param visited the Term to checked if it is a program variable and if true the variable is
     *        added
     *        to the list of found variables
     */
    public void visit(Term visited) {
        if (visited.op() instanceof ProgramVariable variable) {
            result.add(variable);
        }

        if (visited.op() instanceof Modality mod) {
            ProgramVariableCollector pvc =
                new ProgramVariableCollector(mod.program().program(), services);
            pvc.start();
            result.addAll(pvc.result());
        }
    }

    public HashSet<ProgramVariable> result() {
        return result;
    }
}
