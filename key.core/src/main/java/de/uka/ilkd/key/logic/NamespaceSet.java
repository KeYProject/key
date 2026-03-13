/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;


import de.uka.ilkd.key.logic.op.IProgramVariable;

import org.key_project.logic.Choice;
import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleSet;

import org.jspecify.annotations.NonNull;

public class NamespaceSet {

    private Namespace<@NonNull QuantifiableVariable> varNS = new Namespace<>();
    private Namespace<@NonNull IProgramVariable> progVarNS = new Namespace<>();
    // TODO: Operators should not be local to goals
    private Namespace<@NonNull Function> funcNS = new Namespace<>();
    private Namespace<@NonNull RuleSet> ruleSetNS = new Namespace<>();
    private Namespace<@NonNull Sort> sortNS = new Namespace<>();
    private Namespace<@NonNull Choice> choiceNS = new Namespace<>();

    public NamespaceSet() {
    }

    public NamespaceSet(Namespace<@NonNull QuantifiableVariable> varNS,
            Namespace<@NonNull Function> funcNS,
            Namespace<@NonNull Sort> sortNS, Namespace<@NonNull RuleSet> ruleSetNS,
            Namespace<@NonNull Choice> choiceNS,
            Namespace<@NonNull IProgramVariable> programVarNS) {
        this.varNS = varNS;
        this.progVarNS = programVarNS;
        this.funcNS = funcNS;
        this.sortNS = sortNS;
        this.ruleSetNS = ruleSetNS;
        this.choiceNS = choiceNS;
    }

    public NamespaceSet copy() {
        return new NamespaceSet(variables().copy(), functions().copy(),
            sorts().copy(),
            ruleSets().copy(), choices().copy(), programVariables().copy());
    }

    public NamespaceSet shallowCopy() {
        return new NamespaceSet(variables(), functions(), sorts(), ruleSets(),
            choices(),
            programVariables());
    }

    // TODO MU: Rename into sth with wrap or similar
    public NamespaceSet copyWithParent() {
        return new NamespaceSet(new Namespace<>(variables()),
            new Namespace<>(functions()), new Namespace<>(sorts()),
            new Namespace<>(ruleSets()), new Namespace<>(choices()),
            new Namespace<>(programVariables()));
    }

    public Namespace<@NonNull QuantifiableVariable> variables() {
        return varNS;
    }

    public void setVariables(Namespace<@NonNull QuantifiableVariable> varNS) {
        this.varNS = varNS;
    }

    public Namespace<@NonNull IProgramVariable> programVariables() {
        return progVarNS;
    }

    public void setProgramVariables(Namespace<@NonNull IProgramVariable> progVarNS) {
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
        choices().add(ns.choices());
    }

    /**
     * returns all namespaces in an array
     */
    private Namespace<?>[] asArray() {
        return new Namespace[] { variables(), programVariables(), sorts(), ruleSets(), functions(),
            choices() };
    }

    /**
     * returns all namespaces with symbols that may occur in a real sequent (this means all
     * namespaces without variables, choices and ruleSets)
     */
    private Namespace<?>[] logicAsArray() {
        return new Namespace[] { programVariables(), sorts(), functions() };
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
     * looks up for the symbol in the namespaces sort, functions and programVariables
     *
     * @param name the Name to look up
     * @return the element of the given name or null
     */
    public Named lookupLogicSymbol(Name name) {
        return lookup(name, logicAsArray());
    }

    /**
     * retrieves an object of the given name from the namespaces; the first object found in order of
     * the
     * specified namespaces
     *
     * @param name the Name to look up
     * @param spaces the Namespaces where to look for an object of the given name
     * @return the first element with the given name if found in the given namespaces, otherwise
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


    @Override
    public String toString() {
        return "Sorts: " + sorts() + "\n" + "Functions: " + functions() + "\n" + "Variables: "
            + variables() + "\n" + "ProgramVariables: " + programVariables() + "\n" + "Heuristics: "
            + ruleSets() + "\n" + "Taclet Options: " + choices() + "\n";
    }


    public <T extends Name> boolean containsAll(Iterable<T> names) {
        for (Name name : names) {
            if (lookupLogicSymbol(name) == null) {
                return false;
            }
        }
        return true;
    }

    public void seal() {
        varNS.seal();
        progVarNS.seal();
        funcNS.seal();
        ruleSetNS.seal();
        sortNS.seal();
        choiceNS.seal();
    }

    public boolean isEmpty() {
        return varNS.isEmpty() && programVariables().isEmpty() && funcNS.isEmpty()
                && ruleSetNS.isEmpty() && sortNS.isEmpty() && choiceNS.isEmpty();
    }


    // create a namespace
    public NamespaceSet simplify() {
        return new NamespaceSet(varNS.simplify(), funcNS.simplify(), sortNS.simplify(),
            ruleSetNS.simplify(), choiceNS.simplify(), progVarNS.simplify());
    }

    public NamespaceSet getCompression() {
        return new NamespaceSet(varNS.compress(), funcNS.compress(), sortNS.compress(),
            ruleSetNS.compress(), choiceNS.compress(), progVarNS.compress());
    }

    public void flushToParent() {
        for (Namespace<?> ns : asArray()) {
            ns.flushToParent();
        }
    }

    public NamespaceSet getParent() {
        return new NamespaceSet(varNS.parent(), funcNS.parent(), sortNS.parent(),
            ruleSetNS.parent(), choiceNS.parent(), progVarNS.parent());
    }

}
