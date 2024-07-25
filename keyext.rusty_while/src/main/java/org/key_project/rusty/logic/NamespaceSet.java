/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.op.ProgramVariable;

import org.jspecify.annotations.NonNull;

public class NamespaceSet {
    private Namespace<@NonNull QuantifiableVariable> varNS = new Namespace<>();
    private Namespace<@NonNull ProgramVariable> progVarNS = new Namespace<>();
    // TODO: Operators should not be local to goals
    private Namespace<@NonNull Function> funcNS = new Namespace<>();
    private Namespace<@NonNull Sort> sortNS = new Namespace<>();

    public NamespaceSet() {}

    public NamespaceSet(Namespace<@NonNull QuantifiableVariable> varNS,
            Namespace<@NonNull ProgramVariable> progVarNS, Namespace<@NonNull Function> funcNS,
            Namespace<@NonNull Sort> sortNS) {
        this.varNS = varNS;
        this.progVarNS = progVarNS;
        this.funcNS = funcNS;
        this.sortNS = sortNS;
    }

    public Namespace<@NonNull QuantifiableVariable> variables() {
        return varNS;
    }

    public void setVariables(Namespace<@NonNull QuantifiableVariable> varNS) {
        this.varNS = varNS;
    }

    public Namespace<@NonNull ProgramVariable> programVariables() {
        return progVarNS;
    }

    public void setProgramVariables(Namespace<@NonNull ProgramVariable> progVarNS) {
        this.progVarNS = progVarNS;
    }

    public Namespace<@NonNull Function> functions() {
        return funcNS;
    }

    public void setFunctions(Namespace<@NonNull Function> funcNS) {
        this.funcNS = funcNS;
    }

    public Namespace<@NonNull Sort> sorts() {
        return sortNS;
    }

    public void setSorts(Namespace<@NonNull Sort> sortNS) {
        this.sortNS = sortNS;
    }

    public void add(NamespaceSet ns) {
        variables().add(ns.variables());
        programVariables().add(ns.programVariables());
        sorts().add(ns.sorts());
        functions().add(ns.functions());
    }

    public NamespaceSet copy() {
        return new NamespaceSet(variables().copy(), programVariables().copy(), functions().copy(),
            sorts().copy());
    }

    @Override
    public String toString() {
        return "Sorts: " + sorts() + "\n" + "Functions: " + functions() + "\n" + "Variables: "
            + variables() + "\n" + "ProgramVariables: " + programVariables() + "\n";
    }
}
