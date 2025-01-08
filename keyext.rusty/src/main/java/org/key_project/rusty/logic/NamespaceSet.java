/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleSet;
import org.key_project.rusty.logic.op.ProgramVariable;

import org.jspecify.annotations.NonNull;

public class NamespaceSet {
    private Namespace<@NonNull QuantifiableVariable> varNS = new Namespace<>();
    private Namespace<@NonNull ProgramVariable> progVarNS = new Namespace<>();
    // TODO: Operators should not be local to goals
    private Namespace<@NonNull Function> funcNS = new Namespace<>();
    private Namespace<@NonNull RuleSet> ruleSetNS = new Namespace<>();
    private Namespace<@NonNull Sort> sortNS = new Namespace<>();
    private Namespace<@NonNull Choice> choiceNS = new Namespace<>();

    public NamespaceSet() {}

    public NamespaceSet(Namespace<@NonNull QuantifiableVariable> varNS,
            Namespace<@NonNull ProgramVariable> progVarNS, Namespace<@NonNull Function> funcNS,
            Namespace<@NonNull Choice> choiceNS,
            Namespace<@NonNull Sort> sortNS) {
        assert varNS != null;
        this.varNS = varNS;
        this.progVarNS = progVarNS;
        this.funcNS = funcNS;
        this.choiceNS = choiceNS;
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

    public Namespace<@NonNull RuleSet> ruleSets() {
        return ruleSetNS;
    }

    public void setRuleSets(Namespace<@NonNull RuleSet> ruleSetNS) {
        this.ruleSetNS = ruleSetNS;
    }

    public Namespace<@NonNull Sort> sorts() {
        return sortNS;
    }

    public void setSorts(Namespace<@NonNull Sort> sortNS) {
        this.sortNS = sortNS;
    }

    public Namespace<@NonNull Choice> choices() {
        return choiceNS;
    }

    public void setChoices(Namespace<@NonNull Choice> choiceNS) {
        this.choiceNS = choiceNS;
    }

    public void add(NamespaceSet ns) {
        variables().add(ns.variables());
        programVariables().add(ns.programVariables());
        sorts().add(ns.sorts());
        ruleSets().add(ns.ruleSets());
        functions().add(ns.functions());
    }

    /**
     * returns all namespaces in an array
     */
    private Namespace<?>[] asArray() {
        return new Namespace[] { variables(), programVariables(), sorts(), ruleSets(), functions(),
        };
    }

    /**
     * looks up if the given name is found in one of the namespaces and returns the named object or
     * null if no object with the same name has been found
     */
    public Named lookup(Name name) {
        final Namespace<?>[] spaces = asArray();
        return lookup(name, spaces);
    }

    /**
     * @param name
     * @param spaces
     * @return the element with the given name if found in the given namespaces, otherwise
     *         <tt>null</tt>
     */
    private Named lookup(Name name, final Namespace<?>[] spaces) {
        for (Namespace<?> space : spaces) {
            final Named n = space.lookup(name);
            if (n != null) {
                return n;
            }
        }
        return null;
    }

    public NamespaceSet copy() {
        return new NamespaceSet(variables().copy(), programVariables().copy(), functions().copy(),
            choiceNS.copy(),
            sorts().copy());
    }

    @Override
    public String toString() {
        return "Sorts: " + sorts() + "\n" + "Functions: " + functions() + "\n" + "Variables: "
            + variables() + "\n" + "ProgramVariables: " + programVariables() + "\n" + "Choices: "
            + choices();
    }

    /**
     * looks up for the symbol in the namespaces sort, functions and programVariables
     *
     * @param name the Name to look up
     * @return the element of the given name or null
     */
    public Named lookupLogicSymbol(Name name) {
        return lookup(name, logicAsArray());
    }

    /**
     * returns all namespaces with symbols that may occur in a real sequent (this means all
     * namespaces without variables, choices and ruleSets)
     */
    private Namespace<?>[] logicAsArray() {
        return new Namespace[] { programVariables(), sorts(), functions() };
    }

    public void flushToParent() {
        for (Namespace<?> ns : asArray()) {
            ns.flushToParent();
        }
    }

    public NamespaceSet getParent() {
        return new NamespaceSet(varNS.parent(), progVarNS.parent(), funcNS.parent(),
            choiceNS.parent(), sortNS.parent());
    }

    // TODO MU: Rename into sth with wrap or similar
    public NamespaceSet copyWithParent() {
        return new NamespaceSet(new Namespace<>(variables()),
            new Namespace<>(programVariables()), new Namespace<>(functions()),
            new Namespace<>(choices()),
            new Namespace<>(sorts()));
    }
}
