/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;



import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ParametricFunctionDecl;
import de.uka.ilkd.key.logic.sort.ParametricSortDecl;
import de.uka.ilkd.key.logic.sort.SortAlias;

import org.key_project.logic.Choice;
import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleSet;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


@NullMarked
public class NamespaceSet {

    private Namespace<QuantifiableVariable> varNS = new Namespace<>();
    private Namespace<IProgramVariable> progVarNS = new Namespace<>();
    // TODO: Operators should not be local to goals
    private Namespace<Function> funcNS = new Namespace<>();
    private Namespace<RuleSet> ruleSetNS = new Namespace<>();
    private Namespace<Sort> sortNS = new Namespace<>();
    private Namespace<@NonNull SortAlias> sortAliases = new Namespace<>();
    private Namespace<ParametricSortDecl> parametricSortNS = new Namespace<>();
    private Namespace<ParametricFunctionDecl> parametricFuncNS = new Namespace<>();
    private Namespace<Choice> choiceNS = new Namespace<>();
    private final DocSpace documentation = new DocSpace();

    public NamespaceSet() {
    }

    public NamespaceSet(Namespace<QuantifiableVariable> varNS,
            Namespace<Function> funcNS,
            Namespace<Sort> sortNS,
            Namespace<SortAlias> sortAliases,
            Namespace<RuleSet> ruleSetNS,
            Namespace<ParametricSortDecl> parametricSortNS,
            Namespace<ParametricFunctionDecl> parametricFuncNS,
            Namespace<Choice> choiceNS,
            Namespace<IProgramVariable> programVarNS) {
        this(varNS, funcNS, sortNS, sortAliases, ruleSetNS,
            parametricSortNS, parametricFuncNS,
            choiceNS, programVarNS, new DocSpace());
    }

    public NamespaceSet(Namespace<QuantifiableVariable> varNS,
            Namespace<Function> funcNS,
            Namespace<Sort> sortNS,
            Namespace<SortAlias> sortAliases,
            Namespace<RuleSet> ruleSetNS,
            Namespace<ParametricSortDecl> parametricSortNS,
            Namespace<ParametricFunctionDecl> parametricFuncNS,
            Namespace<Choice> choiceNS,
            Namespace<IProgramVariable> programVarNS,
            DocSpace documentation) {
        this.varNS = varNS;
        this.progVarNS = programVarNS;
        this.funcNS = funcNS;
        this.sortNS = sortNS;
        this.sortAliases = sortAliases;
        this.ruleSetNS = ruleSetNS;
        this.choiceNS = choiceNS;
        this.parametricSortNS = parametricSortNS;
        this.parametricFuncNS = parametricFuncNS;
        this.documentation.add(documentation);
    }


    public NamespaceSet copy() {
        return new NamespaceSet(variables().copy(), functions().copy(),
            sorts().copy(), sortAliases().copy(),
            ruleSets().copy(), parametricSortNS.copy(), parametricFuncNS.copy(), choices().copy(),
            programVariables().copy(),
            documentation.copy());
    }

    public NamespaceSet shallowCopy() {
        return new NamespaceSet(variables(), functions(), sorts(), sortAliases(), ruleSets(),
            parametricSorts(),
            parametricFunctions(),
            choices(), programVariables(), new DocSpace(documentation));
    }

    // TODO MU: Rename into sth with wrap or similar
    public NamespaceSet copyWithParent() {
        return new NamespaceSet(new Namespace<>(variables()),
            new Namespace<>(functions()), new Namespace<>(sorts()), new Namespace<>(sortAliases()),
            new Namespace<>(ruleSets()), new Namespace<>(parametricSorts()),
            new Namespace<>(parametricFunctions()), new Namespace<>(choices()),
            new Namespace<>(programVariables()),
            new DocSpace(documentation));
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

    public Namespace<@NonNull SortAlias> sortAliases() {
        return sortAliases;
    }

    public void setSortAliases(Namespace<@NonNull SortAlias> sortAliases) {
        this.sortAliases = sortAliases;
    }

    public Namespace<ParametricSortDecl> parametricSorts() {
        return parametricSortNS;
    }

    public void setParametricSorts(Namespace<ParametricSortDecl> parametricSortNS) {
        this.parametricSortNS = parametricSortNS;
    }

    public Namespace<ParametricFunctionDecl> parametricFunctions() {
        return parametricFuncNS;
    }

    public void setParametricFunctions(
            Namespace<ParametricFunctionDecl> parametricFuncNS) {
        this.parametricFuncNS = parametricFuncNS;
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
        sortAliases().add(ns.sortAliases());
        parametricFunctions().add(ns.parametricFunctions());
        parametricSorts().add(ns.parametricSorts());
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
        return new Namespace[] { programVariables(), sorts(), sortAliases(), functions() };
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

    public @Nullable Sort lookupSortOrAlias(String name) {
        return lookupSortOrAlias(new Name(name));
    }

    public @Nullable Sort lookupSortOrAlias(Name name) {
        var sort = sorts().lookup(name);
        if (sort != null)
            return sort;
        SortAlias alias = sortAliases.lookup(name);
        if (alias != null)
            return alias.aliasedSort();
        return null;
    }

    @Override
    public String toString() {
        return "Sorts: " + sorts() + "\n" + "Alias sorts: " + sortAliases() + "\n"
            + "Parametric sorts: " + parametricSorts() + "\n" + "Functions: " + functions() + "\n"
            + "Parametric functions: " + parametricFunctions() + "\n" + "Variables: "
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
        parametricFuncNS.seal();
        ruleSetNS.seal();
        sortNS.seal();
        sortAliases.seal();
        parametricSortNS.seal();
        choiceNS.seal();
    }

    public boolean isEmpty() {
        return varNS.isEmpty() && programVariables().isEmpty() && funcNS.isEmpty()
                && parametricFuncNS.isEmpty()
                && ruleSetNS.isEmpty() && sortNS.isEmpty() && sortAliases.isEmpty()
                && parametricSortNS.isEmpty() && choiceNS.isEmpty();
    }


    // create a namespace
    public NamespaceSet simplify() {
        return new NamespaceSet(varNS.simplify(), funcNS.simplify(), sortNS.simplify(),
            sortAliases.simplify(),
            ruleSetNS.simplify(), parametricSortNS.simplify(), parametricFuncNS.simplify(),
            choiceNS.simplify(), progVarNS.simplify());
    }

    public NamespaceSet getCompression() {
        return new NamespaceSet(varNS.compress(), funcNS.compress(), sortNS.compress(),
            sortAliases.compress(),
            ruleSetNS.compress(), parametricSortNS.compress(), parametricFuncNS.compress(),
            choiceNS.compress(), progVarNS.compress(), documentation);
    }

    public void flushToParent() {
        for (Namespace<?> ns : asArray()) {
            ns.flushToParent();
        }
    }

    public NamespaceSet getParent() {
        return new NamespaceSet(varNS.parent(), funcNS.parent(), sortNS.parent(),
            sortAliases.parent(),
            ruleSetNS.parent(), parametricSortNS.parent(), parametricFuncNS.parent(),
            choiceNS.parent(), progVarNS.parent(), documentation.parent());
    }

    public DocSpace docs() {
        return documentation;
    }
}
