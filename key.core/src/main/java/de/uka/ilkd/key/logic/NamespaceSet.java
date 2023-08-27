/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.RuleSet;

public class NamespaceSet {

    private Namespace<QuantifiableVariable> varNS = new Namespace<>();
    private Namespace<IProgramVariable> progVarNS = new Namespace<>();
    private Namespace<Function> funcNS = new Namespace<>();
    private Namespace<RuleSet> ruleSetNS = new Namespace<>();
    private Namespace<Sort> sortNS = new Namespace<>();
    private Namespace<Choice> choiceNS = new Namespace<>();

    public NamespaceSet() {
    }

    public NamespaceSet(Namespace<QuantifiableVariable> varNS, Namespace<Function> funcNS,
            Namespace<Sort> sortNS, Namespace<RuleSet> ruleSetNS, Namespace<Choice> choiceNS,
            Namespace<IProgramVariable> programVarNS) {
        this.varNS = varNS;
        this.progVarNS = programVarNS;
        this.funcNS = funcNS;
        this.sortNS = sortNS;
        this.ruleSetNS = ruleSetNS;
        this.choiceNS = choiceNS;
    }

    public NamespaceSet copy() {
        return new NamespaceSet(variables().copy(), functions().copy(), sorts().copy(),
            ruleSets().copy(), choices().copy(), programVariables().copy());
    }

    public NamespaceSet shallowCopy() {
        return new NamespaceSet(variables(), functions(), sorts(), ruleSets(), choices(),
            programVariables());
    }

    // TODO MU: Rename into sth with wrap or similar
    public NamespaceSet copyWithParent() {
        return new NamespaceSet(new Namespace<>(variables()),
            new Namespace<>(functions()), new Namespace<>(sorts()),
            new Namespace<>(ruleSets()), new Namespace<>(choices()),
            new Namespace<>(programVariables()));
    }

    public Namespace<QuantifiableVariable> variables() {
        return varNS;
    }

    public void setVariables(Namespace<QuantifiableVariable> varNS) {
        this.varNS = varNS;
    }

    public Namespace<IProgramVariable> programVariables() {
        return progVarNS;
    }

    public void setProgramVariables(Namespace<IProgramVariable> progVarNS) {
        this.progVarNS = progVarNS;
    }

    public Namespace<Function> functions() {
        return funcNS;
    }

    public void setFunctions(Namespace<Function> funcNS) {
        this.funcNS = funcNS;
    }

    public Namespace<RuleSet> ruleSets() {
        return ruleSetNS;
    }

    public void setRuleSets(Namespace<RuleSet> ruleSetNS) {
        this.ruleSetNS = ruleSetNS;
    }

    public Namespace<Sort> sorts() {
        return sortNS;
    }

    public void setSorts(Namespace<Sort> sortNS) {
        this.sortNS = sortNS;
    }

    public Namespace<Choice> choices() {
        return choiceNS;
    }

    public void setChoices(Namespace<Choice> choiceNS) {
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
