/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po;

import java.util.LinkedList;
import java.util.TreeSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosTableLayouter;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.logic.Named;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.SortedOperator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

public class InfFlowProofSymbols {

    private boolean isFreshContract;

    private ImmutableSet<Pair<Sort, Boolean>> sorts =
        DefaultImmutableSet.nil();

    private ImmutableSet<Pair<Function, Boolean>> predicates =
        DefaultImmutableSet.nil();

    private ImmutableSet<Pair<Function, Boolean>> functions =
        DefaultImmutableSet.nil();

    private ImmutableSet<Pair<ProgramVariable, Boolean>> programVariables =
        DefaultImmutableSet.nil();

    private ImmutableSet<Pair<SchemaVariable, Boolean>> schemaVariables =
        DefaultImmutableSet.nil();

    private ImmutableSet<Pair<Taclet, Boolean>> taclets =
        DefaultImmutableSet.nil();

    /*
     * private static final ImmutableSet<String> tacletPrefixes =
     * DefaultImmutableSet.<String>nil().add("unfold_computed_formula")
     * .add("Class_invariant_axiom") .add("Use_information_flow_contract") .add("Split_post")
     * .add("Remove_post");
     */

    public InfFlowProofSymbols() {
        isFreshContract = true;
    }

    /*
     * public InfFlowProofSymbols(ImmutableSet<Taclet> taclets) { this(); String name = null; for
     * (Taclet t: taclets) { name = t.name().toString(); if (t instanceof RewriteTaclet) for (String
     * s: tacletPrefixes) { if (name.startsWith(s)) { add(t); } } } }
     */

    private InfFlowProofSymbols getLabeledSymbols() {
        InfFlowProofSymbols symbols = new InfFlowProofSymbols();
        if (!isFreshContract()) {
            symbols.useProofSymbols();
        }
        symbols.sorts = getLabeledSorts();
        symbols.predicates = getLabeledPredicates();
        symbols.functions = getLabeledFunctions();
        symbols.programVariables = getLabeledProgramVariables();
        symbols.schemaVariables = getLabeledSchemaVariables();
        symbols.taclets = getLabeledTaclets();
        return symbols;
    }

    private ImmutableSet<Pair<Sort, Boolean>> getLabeledSorts() {
        ImmutableSet<Pair<Sort, Boolean>> labeledSorts =
            DefaultImmutableSet.nil();
        for (Pair<Sort, Boolean> s : sorts) {
            if (s.second) {
                labeledSorts = labeledSorts.add(new Pair<>(s.first, false));
            }
        }
        return labeledSorts;
    }

    private ImmutableSet<Pair<Function, Boolean>> getLabeledPredicates() {
        ImmutableSet<Pair<Function, Boolean>> labeledPredicates =
            DefaultImmutableSet.nil();
        for (Pair<Function, Boolean> p : predicates) {
            if (p.second) {
                labeledPredicates =
                    labeledPredicates.add(new Pair<>(p.first, false));
            }
        }
        return labeledPredicates;
    }

    private ImmutableSet<Pair<Function, Boolean>> getLabeledFunctions() {
        ImmutableSet<Pair<Function, Boolean>> labeledFunctions =
            DefaultImmutableSet.nil();
        for (Pair<Function, Boolean> f : functions) {
            if (f.second) {
                labeledFunctions =
                    labeledFunctions.add(new Pair<>(f.first, false));
            }
        }
        return labeledFunctions;
    }

    private ImmutableSet<Pair<ProgramVariable, Boolean>> getLabeledProgramVariables() {
        ImmutableSet<Pair<ProgramVariable, Boolean>> labeledProgramVariables =
            DefaultImmutableSet.nil();
        for (Pair<ProgramVariable, Boolean> pv : programVariables) {
            if (pv.second) {
                labeledProgramVariables = labeledProgramVariables
                        .add(new Pair<>(pv.first, false));
            }
        }
        return labeledProgramVariables;
    }

    private ImmutableSet<Pair<SchemaVariable, Boolean>> getLabeledSchemaVariables() {
        ImmutableSet<Pair<SchemaVariable, Boolean>> labeledSchemaVariables =
            DefaultImmutableSet.nil();
        for (Pair<SchemaVariable, Boolean> sv : schemaVariables) {
            if (sv.second) {
                labeledSchemaVariables =
                    labeledSchemaVariables.add(new Pair<>(sv.first, false));
            }
        }
        return labeledSchemaVariables;
    }

    private ImmutableSet<Pair<Taclet, Boolean>> getLabeledTaclets() {
        ImmutableSet<Pair<Taclet, Boolean>> labeledTaclets =
            DefaultImmutableSet.nil();
        for (Pair<Taclet, Boolean> t : taclets) {
            if (t.second) {
                labeledTaclets = labeledTaclets.add(new Pair<>(t.first, false));
            }
        }
        return labeledTaclets;
    }

    private boolean containsSort(Sort s) {
        ImmutableSet<Pair<Sort, Boolean>> ps = DefaultImmutableSet.<Pair<Sort, Boolean>>nil()
                .add(new Pair<>(s, true)).add(new Pair<>(s, false));
        for (Pair<Sort, Boolean> p : sorts) {
            if (ps.contains(p)) {
                return true;
            }
        }
        return false;
    }

    private boolean containsPredicate(Function f) {
        ImmutableSet<Pair<Function, Boolean>> ps = DefaultImmutableSet
                .<Pair<Function, Boolean>>nil().add(new Pair<>(f, true))
                .add(new Pair<>(f, false));
        if (!f.name().toString().startsWith("RELATED_BY")
                && !f.name().toString().startsWith("EXECUTION_OF")) {
            return false;
        }
        for (Pair<Function, Boolean> p : predicates) {
            if (ps.contains(p)) {
                return true;
            }
        }
        return false;
    }

    private boolean containsFunction(Function f) {
        ImmutableSet<Pair<Function, Boolean>> ps = DefaultImmutableSet
                .<Pair<Function, Boolean>>nil().add(new Pair<>(f, true))
                .add(new Pair<>(f, false));
        for (Pair<Function, Boolean> p : functions) {
            if (ps.contains(p)) {
                return true;
            }
        }
        return false;
    }

    private boolean containsProgramVariable(ProgramVariable pv) {
        ImmutableSet<Pair<ProgramVariable, Boolean>> ps =
            DefaultImmutableSet.<Pair<ProgramVariable, Boolean>>nil()
                    .add(new Pair<>(pv, true))
                    .add(new Pair<>(pv, false));
        for (Pair<ProgramVariable, Boolean> p : programVariables) {
            if (ps.contains(p)) {
                return true;
            }
        }
        return false;
    }

    private boolean containsSchemaVariable(SchemaVariable sv) {
        ImmutableSet<Pair<SchemaVariable, Boolean>> ps =
            DefaultImmutableSet.<Pair<SchemaVariable, Boolean>>nil()
                    .add(new Pair<>(sv, true))
                    .add(new Pair<>(sv, false));
        for (Pair<SchemaVariable, Boolean> p : schemaVariables) {
            if (ps.contains(p)) {
                return true;
            }
        }
        return false;
    }

    private boolean containsTaclet(Taclet t) {
        ImmutableSet<Pair<Taclet, Boolean>> ps = DefaultImmutableSet.<Pair<Taclet, Boolean>>nil()
                .add(new Pair<>(t, true)).add(new Pair<>(t, false));
        for (Pair<Taclet, Boolean> p : taclets) {
            if (ps.contains(p)) {
                return true;
            }
        }
        return false;
    }

    private void addTaclet(Taclet t, boolean labeled) {
        if (!containsTaclet(t)) {
            taclets = taclets.add(new Pair<>(t, !labeled));
        }
    }

    private void addSort(Sort s, boolean labeled) {
        if (!(s instanceof NullSort) && !containsSort(s)) {
            sorts = sorts.add(new Pair<>(s, !labeled));
        }
    }

    private boolean isPredicate(Operator f) {
        assert f != null;
        return f.name().toString().startsWith("RELATED_BY")
                || f.name().toString().startsWith("EXECUTION_OF");
    }

    private void addPredicate(Function p, boolean labeled) {
        if (!containsPredicate(p)) {
            predicates = predicates.add(new Pair<>(p, !labeled));
        }
    }

    private void addFunction(Function f, boolean labeled) {
        if (!containsFunction(f)) {
            functions = functions.add(new Pair<>(f, !labeled));
        }
    }

    private void addFunc(Function f, boolean labeled) {
        if (isPredicate(f)) {
            addPredicate(f, labeled);
        } else {
            addFunction(f, labeled);
        }
    }

    private void addSchemaVariable(SchemaVariable sv, boolean labeled) {
        if (!containsSchemaVariable(sv)) {
            schemaVariables = schemaVariables.add(new Pair<>(sv, !labeled));
        }
    }

    private void addProgramVariable(ProgramVariable pv, boolean labeled) {
        if (!containsProgramVariable(pv)) {
            programVariables =
                programVariables.add(new Pair<>(pv, !labeled));
        }
    }

    public void useProofSymbols() {
        this.isFreshContract = false;
    }

    public boolean isFreshContract() {
        return this.isFreshContract;
    }

    public static ProgramVariable searchPV(String s, Services services) {
        Namespace<IProgramVariable> ns = services.getNamespaces().programVariables();
        IProgramVariable n = ns.lookup(s);
        int i = 0;
        while (n == null && i < 1000) {
            n = ns.lookup(s + "_" + i);
        }
        assert n instanceof ProgramVariable;
        return (ProgramVariable) n;
    }

    public void add(Named symb) {
        assert symb != null;
        boolean l = false;

        if (symb instanceof Sort s) {
            addSort(s, l);
        }
        if (symb instanceof SortedOperator s) {
            addSort(s.sort(), l);
        }
        if (symb instanceof Function f) {
            addFunc(f, l);
        }
        if (symb instanceof ProgramVariable pv) {
            addProgramVariable(pv, l);
        }
        if (symb instanceof SchemaVariable sv) {
            addSchemaVariable(sv, l);
        }
        if (symb instanceof Taclet t) {
            addTaclet(t, l);
        }
    }

    public void addLabeled(Named symb) {
        assert symb != null;
        boolean l = true;

        if (symb instanceof Sort sort) {
            addSort(sort, l);
        }
        if (symb instanceof SortedOperator op) {
            addSort(op.sort(), l);
        }
        if (symb instanceof Function f) {
            addFunc(f, l);
        }
        if (symb instanceof ProgramVariable pv) {
            addProgramVariable(pv, l);
        }
        if (symb instanceof SchemaVariable sv) {
            addSchemaVariable(sv, l);
        }
        if (symb instanceof Taclet t) {
            addTaclet(t, l);
        }
    }

    public void add(JTerm t) {
        assert t != null;
        t = TermBuilder.goBelowUpdates(t);
        if (!isPredicate(t.op())) {
            if (t.arity() > 0) {
                for (final JTerm s : t.subs()) {
                    add(s);
                }
            }
        }
        add(t.op());
    }

    public void addLabeled(JTerm t) {
        assert t != null;
        t = TermBuilder.goBelowUpdates(t);
        if (t.arity() > 0) {
            for (final JTerm s : t.subs()) {
                addLabeled(s);
            }
        }
        addLabeled(t.op());
    }

    public InfFlowProofSymbols union(InfFlowProofSymbols symbols) {
        assert symbols != null;
        InfFlowProofSymbols result = new InfFlowProofSymbols();
        if (!isFreshContract() || !symbols.isFreshContract()) {
            result.useProofSymbols();
        }
        result.sorts = sorts.union(symbols.sorts);
        result.predicates = predicates.union(symbols.predicates);
        result.functions = functions.union(symbols.functions);
        result.programVariables = programVariables.union(symbols.programVariables);
        result.schemaVariables = schemaVariables.union(symbols.schemaVariables);
        result.taclets = taclets.union(symbols.taclets);
        return result;
    }

    public InfFlowProofSymbols unionLabeled(InfFlowProofSymbols symbols) {
        assert symbols != null;
        symbols = symbols.getLabeledSymbols();
        InfFlowProofSymbols result = new InfFlowProofSymbols();
        if (!isFreshContract() || !symbols.isFreshContract()) {
            result.useProofSymbols();
        }
        result.sorts = sorts.union(symbols.sorts);
        result.predicates = predicates.union(symbols.predicates);
        result.functions = functions.union(symbols.functions);
        result.programVariables = programVariables.union(symbols.programVariables);
        result.schemaVariables = schemaVariables.union(symbols.schemaVariables);
        result.taclets = taclets.union(symbols.taclets);
        return result;
    }

    public void addTotalTerm(JTerm t) {
        assert t != null;
        if (t.op() instanceof UpdateApplication) {
            addTotalTerm(UpdateApplication.getUpdate(t));
            addTotalTerm(UpdateApplication.getTarget(t));
        }
        if (t.op() instanceof ElementaryUpdate) {
            add(((ElementaryUpdate) t.op()).lhs());
        }
        t = TermBuilder.goBelowUpdates(t);
        if (t.arity() > 0) {
            for (final JTerm s : t.subs()) {
                addTotalTerm(s);
            }
        }
        add(t.op());
    }

    public void addLabeledTotalTerm(JTerm t) {
        assert t != null;
        if (t.op() instanceof UpdateApplication) {
            addLabeledTotalTerm(UpdateApplication.getUpdate(t));
            addLabeledTotalTerm(UpdateApplication.getTarget(t));
        }
        if (t.op() instanceof ElementaryUpdate) {
            addLabeled(((ElementaryUpdate) t.op()).lhs());
        }
        t = TermBuilder.goBelowUpdates(t);
        if (t.arity() > 0) {
            for (final JTerm s : t.subs()) {
                addLabeledTotalTerm(s);
            }
        }
        addLabeled(t.op());
    }

    private ImmutableSet<Sort> getSorts() {
        ImmutableSet<Sort> sorts = DefaultImmutableSet.nil();
        for (Pair<Sort, Boolean> s : this.sorts) {
            sorts = sorts.add(s.first);
        }
        return sorts;
    }

    private LinkedList<Sort> ensureRightOrderOfSorts(ImmutableSet<Sort> s) {
        LinkedList<TreeSet<Sort>> sortContainers = new LinkedList<>();
        for (final Sort sort : s) {
            boolean added = false;
            for (TreeSet<Sort> container : sortContainers) {
                if (container.add(sort)) {
                    added = true;
                    break;
                }
            }
            if (!added) {
                sortContainers.add(new TreeSet<>((s1, s2) -> {
                    if (s1.extendsTrans(s2)) {
                        return 1;
                    }
                    if (s2.extendsTrans(s1)) {
                        return -1;
                    }
                    return 0;
                }));
                sortContainers.getLast().add(sort);
            }
        }
        LinkedList<Sort> sorts = new LinkedList<>();
        for (final TreeSet<Sort> container : sortContainers) {
            sorts.addAll(container);
        }
        return sorts;
    }

    private LinkedList<Sort> removeArraySorts(LinkedList<Sort> sorts) {
        sorts.removeIf(s -> s instanceof ArraySort);
        return sorts;
    }

    private ImmutableSet<Function> getPredicates() {
        ImmutableSet<Function> predicates = DefaultImmutableSet.nil();
        for (Pair<Function, Boolean> p : this.predicates) {
            predicates = predicates.add(p.first);
        }
        return predicates;
    }

    private ImmutableSet<Function> getFunctions() {
        ImmutableSet<Function> functions = DefaultImmutableSet.nil();
        for (Pair<Function, Boolean> f : this.functions) {
            functions = functions.add(f.first);
        }
        return functions;
    }

    private ImmutableSet<ProgramVariable> getProgramVariables() {
        ImmutableSet<ProgramVariable> programVariables = DefaultImmutableSet.nil();
        for (Pair<ProgramVariable, Boolean> pv : this.programVariables) {
            programVariables = programVariables.add(pv.first);
        }
        return programVariables;
    }

    private ImmutableSet<SchemaVariable> getSchemaVariables() {
        ImmutableSet<SchemaVariable> schemaVariables = DefaultImmutableSet.nil();
        for (Pair<SchemaVariable, Boolean> sv : this.schemaVariables) {
            schemaVariables = schemaVariables.add(sv.first);
        }
        return schemaVariables;
    }

    private ImmutableSet<Taclet> getTaclets() {
        ImmutableSet<Taclet> taclets = DefaultImmutableSet.nil();
        for (Pair<Taclet, Boolean> t : this.taclets) {
            taclets = taclets.add(t.first);
        }
        return taclets;
    }

    private void printSpace(StringBuilder result) {
        result.append("\n\n");
    }

    private void printSorts(StringBuilder result) {
        if (getSorts().isEmpty()) {
            return;
        }

        result.append("\\sorts{\n");
        LinkedList<Sort> sortsList = ensureRightOrderOfSorts(getSorts());
        // bugfix (CS): array types need not be added as sorts
        // (and they cannot be parsed...)
        sortsList = removeArraySorts(sortsList);
        for (final Sort sort : sortsList) {
            result.append(sort.name());
            if (!sort.extendsSorts().isEmpty()) {
                StringBuilder res = new StringBuilder("\\extends ");
                boolean extendsAtLeastOneSort = false;
                for (final Sort sortParent : sort.extendsSorts()) {
                    if (sortParent != JavaDLTheory.ANY) {
                        res.append(sortParent.name()).append(", ");
                        extendsAtLeastOneSort = true;
                    }
                }
                if (extendsAtLeastOneSort) {
                    final int index = res.lastIndexOf(", ");
                    res = new StringBuilder(res.substring(0, index == -1 ? res.length() : index));
                    result.append(res);
                }
            }
            result.append(";\n");
        }
        result.append("}\n\n");
    }

    private void printPredicate(StringBuilder result, Function f) {
        result.append(f.name());
        for (int i = 0; i < f.arity(); i++) {
            result.append(i == 0 ? "(" : ",");
            result.append(f.argSort(i));
            result.append(i == f.arity() - 1 ? ")" : "");
        }
        result.append(";\n");
    }

    private void printPredicates(StringBuilder result) {
        if (getPredicates().isEmpty()) {
            return;
        }

        result.append("\\predicates{\n");
        for (final Function pred : getPredicates()) {
            printPredicate(result, pred);
        }
        result.append("}\n\n");
    }

    private void printFunctions(StringBuilder result) {
        if (getFunctions().isEmpty()) {
            return;
        }

        result.append("\\functions{\n");
        for (final Function f : getFunctions()) {
            result.append(f.sort().name()).append(" ");
            printPredicate(result, f);
        }
        result.append("}\n\n");
    }

    private void printProgramVariables(StringBuilder result) {
        if (getProgramVariables().isEmpty()) {
            return;
        }

        result.append("\\programVariables{\n");
        for (final ProgramVariable pv : getProgramVariables()) {
            result.append(pv.sort().name()).append(" ");
            result.append(pv.name());
            result.append(";\n");
        }
        result.append("}\n\n");
    }

    @SuppressWarnings("unused")
    private void printSchemaVariables(StringBuilder result) {
        if (getSchemaVariables().isEmpty()) {
            return;
        }

        result.append("\\schemaVariables{\n");
        for (final SchemaVariable sv : getSchemaVariables()) {
            if (!(sv instanceof JOperatorSV asv))
                continue;
            final String prefix = asv instanceof FormulaSV ? "\\formula "
                    : asv instanceof TermSV ? "\\term " : "\\variables ";
            result.append(prefix);
            result.append(asv.sort().name()).append(" ");
            result.append(asv.name());
            result.append(";\n");
        }
        result.append("}\n\n");
    }

    private void printTaclets(StringBuilder result) {
        if (getTaclets().isEmpty()) {
            return;
        }

        result.append("\\rules{");
        for (final Taclet taclet : getTaclets()) {
            result.append("\n\n");

            LogicPrinter printer =
                new LogicPrinter(new NotationInfo(), null, PosTableLayouter.pure(80));

            printer.printTaclet(taclet);
            result.append(printer.result()).append(";");
        }
        result.append("\n}");
        result.append("\n\n");
    }

    public String printProofSymbols() {
        StringBuilder result = new StringBuilder();

        printSpace(result);
        printSorts(result);
        printPredicates(result);
        printFunctions(result);
        printProgramVariables(result);
        // printSchemaVariables(result);
        printTaclets(result);

        return result.toString();
    }
}
