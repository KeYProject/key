package de.uka.ilkd.key.proof.init;

import java.util.Comparator;
import java.util.LinkedList;
import java.util.TreeSet;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.pp.StringBackend;
import java.util.Iterator;

public class InfFlowProofSymbols {

    private boolean isFreshContract;

    private ImmutableSet<Pair<Sort, Boolean>> sorts
            = DefaultImmutableSet.<Pair<Sort, Boolean>>nil();

    private ImmutableSet<Pair<Function, Boolean>> predicates
            = DefaultImmutableSet.<Pair<Function, Boolean>>nil();

    private ImmutableSet<Pair<Function, Boolean>> functions
            = DefaultImmutableSet.<Pair<Function, Boolean>>nil();

    private ImmutableSet<Pair<ProgramVariable, Boolean>> programVariables
            = DefaultImmutableSet.<Pair<ProgramVariable, Boolean>>nil();

    private ImmutableSet<Pair<SchemaVariable, Boolean>> schemaVariables
            = DefaultImmutableSet.<Pair<SchemaVariable, Boolean>>nil();

    private ImmutableSet<Pair<Taclet, Boolean>> taclets
            = DefaultImmutableSet.<Pair<Taclet, Boolean>>nil();

    /*private static final ImmutableSet<String> tacletPrefixes
            = DefaultImmutableSet.<String>nil().add("unfold_computed_formula")
                                               .add("Class_invariant_axiom")
                                               .add("Use_information_flow_contract")
                                               .add("Split_post")
                                               .add("Remove_post");*/

    public InfFlowProofSymbols() {
        isFreshContract = true;
    }

    /*public InfFlowProofSymbols(ImmutableSet<Taclet> taclets) {
        this();
        String name = null;
        for (Taclet t: taclets) {
            name = t.name().toString();
            if (t instanceof RewriteTaclet)
            for (String s: tacletPrefixes) {
                if (name.startsWith(s)) {
                    add(t);
                }
            }
        }
    }*/

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
                DefaultImmutableSet.<Pair<Sort, Boolean>>nil();
        for (Pair<Sort, Boolean> s: sorts) {
            if (s.second) {
                labeledSorts = labeledSorts.add(new Pair<Sort, Boolean>(s.first, false));
            }
        }
        return labeledSorts;
    }

    private ImmutableSet<Pair<Function, Boolean>> getLabeledPredicates() {
        ImmutableSet<Pair<Function, Boolean>> labeledPredicates =
                DefaultImmutableSet.<Pair<Function, Boolean>>nil();
        for (Pair<Function, Boolean> p: predicates) {
            if (p.second) {
                labeledPredicates =
                        labeledPredicates.add(new Pair<Function, Boolean>(p.first, false));
            }
        }
        return labeledPredicates;
    }

    private ImmutableSet<Pair<Function, Boolean>> getLabeledFunctions() {
        ImmutableSet<Pair<Function, Boolean>> labeledFunctions =
                DefaultImmutableSet.<Pair<Function, Boolean>>nil();
        for (Pair<Function, Boolean> f: functions) {
            if (f.second) {
                labeledFunctions =
                        labeledFunctions.add(new Pair<Function, Boolean>(f.first, false));
            }
        }
        return labeledFunctions;
    }

    private ImmutableSet<Pair<ProgramVariable, Boolean>> getLabeledProgramVariables() {
        ImmutableSet<Pair<ProgramVariable, Boolean>> labeledProgramVariables =
                DefaultImmutableSet.<Pair<ProgramVariable, Boolean>>nil();
        for (Pair<ProgramVariable, Boolean> pv: programVariables) {
            if (pv.second) {
                labeledProgramVariables = labeledProgramVariables.add(
                        new Pair<ProgramVariable, Boolean>(pv.first, false));
            }
        }
        return labeledProgramVariables;
    }

    private ImmutableSet<Pair<SchemaVariable, Boolean>> getLabeledSchemaVariables() {
        ImmutableSet<Pair<SchemaVariable, Boolean>> labeledSchemaVariables =
                DefaultImmutableSet.<Pair<SchemaVariable, Boolean>>nil();
        for (Pair<SchemaVariable, Boolean> sv: schemaVariables) {
            if (sv.second) {
                labeledSchemaVariables = labeledSchemaVariables.add(
                        new Pair<SchemaVariable, Boolean>(sv.first, false));
            }
        }
        return labeledSchemaVariables;
    }

    private ImmutableSet<Pair<Taclet, Boolean>> getLabeledTaclets() {
        ImmutableSet<Pair<Taclet, Boolean>> labeledTaclets =
                DefaultImmutableSet.<Pair<Taclet, Boolean>>nil();
        for (Pair<Taclet, Boolean> t: taclets) {
            if (t.second) {
                labeledTaclets = labeledTaclets.add(new Pair<Taclet, Boolean>(t.first, false));
            }
        }
        return labeledTaclets;
    }

    private boolean containsSort(Sort s) {
        ImmutableSet<Pair<Sort, Boolean>> ps =
                DefaultImmutableSet.<Pair<Sort, Boolean>>nil()
                .add(new Pair<Sort, Boolean> (s, true))
                .add(new Pair<Sort, Boolean> (s, false));
        for (Pair<Sort, Boolean> p: sorts) {
            if (ps.contains(p)) {
                return true;
            }
        }
        return false;
    }

    private boolean containsPredicate(Function f) {
        ImmutableSet<Pair<Function, Boolean>> ps =
                DefaultImmutableSet.<Pair<Function, Boolean>>nil()
                .add(new Pair<Function, Boolean> (f, true))
                .add(new Pair<Function, Boolean> (f, false));
        if (!f.name().toString().startsWith("RELATED_BY") &&
                !f.name().toString().startsWith("EXECUTION_OF")) {
            return false;
        }
        for (Pair<Function, Boolean> p: predicates) {
            if (ps.contains(p)) {
                return true;
            }
        }
        return false;
    }

    private boolean containsFunction(Function f) {
        ImmutableSet<Pair<Function, Boolean>> ps =
                DefaultImmutableSet.<Pair<Function, Boolean>>nil()
                .add(new Pair<Function, Boolean> (f, true))
                .add(new Pair<Function, Boolean> (f, false));
        for (Pair<Function, Boolean> p: functions) {
            if (ps.contains(p)) {
                return true;
            }
        }
        return false;
    }

    private boolean containsProgramVariable(ProgramVariable pv) {
        ImmutableSet<Pair<ProgramVariable, Boolean>> ps =
                DefaultImmutableSet.<Pair<ProgramVariable, Boolean>>nil()
                .add(new Pair<ProgramVariable, Boolean> (pv, true))
                .add(new Pair<ProgramVariable, Boolean> (pv, false));
        for (Pair<ProgramVariable, Boolean> p: programVariables) {
            if (ps.contains(p)) {
                return true;
            }
        }
        return false;
    }

    private boolean containsSchemaVariable(SchemaVariable sv) {
        ImmutableSet<Pair<SchemaVariable, Boolean>> ps =
                DefaultImmutableSet.<Pair<SchemaVariable, Boolean>>nil()
                .add(new Pair<SchemaVariable, Boolean> (sv, true))
                .add(new Pair<SchemaVariable, Boolean> (sv, false));
        for (Pair<SchemaVariable, Boolean> p: schemaVariables) {
            if (ps.contains(p)) {
                return true;
            }
        }
        return false;
    }

    private boolean containsTaclet(Taclet t) {
        ImmutableSet<Pair<Taclet, Boolean>> ps =
                DefaultImmutableSet.<Pair<Taclet, Boolean>>nil()
                .add(new Pair<Taclet, Boolean> (t, true))
                .add(new Pair<Taclet, Boolean> (t, false));
        for (Pair<Taclet, Boolean> p: taclets) {
            if (ps.contains(p)) {
                return true;
            }
        }
        return false;
    }

    private void addTaclet(Taclet t, boolean labeled) {
        if (!containsTaclet(t)) {
            taclets = taclets.add(new Pair<Taclet, Boolean>(t, !labeled));
        }
    }

    private void addSort(Sort s, boolean labeled) {
        if (!(s instanceof NullSort) &&
                !containsSort(s)) {
            sorts = sorts.add(new Pair<Sort, Boolean>(s, !labeled));
        }
    }

    private boolean isPredicate(Operator f) {
        assert f != null;
        if (f.name().toString().startsWith("RELATED_BY") ||
                f.name().toString().startsWith("EXECUTION_OF")) {
            return true;
        } else {
            return false;
        }
    }

    private void addPredicate (Function p, boolean labeled) {
        if (!containsPredicate(p)) {
            predicates = predicates.add(new Pair<Function, Boolean>(p, !labeled));
        }
    }

    private void addFunction (Function f, boolean labeled) {
        if (!containsFunction(f))
            functions = functions.add(new Pair<Function, Boolean>(f, !labeled));
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
            schemaVariables = schemaVariables.add(new Pair<SchemaVariable, Boolean>(sv, !labeled));
        }
    }

    private void addProgramVariable(ProgramVariable pv, boolean labeled) {
        if (!containsProgramVariable(pv)) {
            programVariables = programVariables.add(new Pair<ProgramVariable, Boolean>(pv, !labeled));
        }
    }

    public void useProofSymbols() {
        this.isFreshContract = false;
    }

    public boolean isFreshContract() {
        return this.isFreshContract;
    }

    public static ProgramVariable searchPV(String s, Services services) {
        Namespace ns = services.getNamespaces().programVariables();
        Named n = ns.lookup(s);
        int i = 0;
        while (n == null && i < 1000) {
            n = ns.lookup(s + "_" + i);
        }
        assert n instanceof ProgramVariable;
        return (ProgramVariable)n;
    }

    public void add(Named symb) {
        assert symb != null;
        boolean l = false;

        if (symb instanceof Sort) {
            final Sort s = (Sort)symb;
            addSort(s, l);
        }
        if (symb instanceof SortedOperator) {
            final SortedOperator s = (SortedOperator)symb;
            addSort(s.sort(), l);
        }
        if (symb instanceof Function) {
            final Function f = (Function)symb;
            addFunc(f, l);
        }
        if (symb instanceof ProgramVariable) {
            final ProgramVariable pv = (ProgramVariable)symb;
            addProgramVariable(pv, l);
        }
        if (symb instanceof SchemaVariable) {
            final SchemaVariable sv = (SchemaVariable)symb;
            addSchemaVariable(sv, l);
        }
        if (symb instanceof Taclet) {
            final Taclet t = (Taclet)symb;
            addTaclet(t, l);
        }
    }

    public void addLabeled(Named symb) {
        assert symb != null;
        boolean l = true;

        if (symb instanceof Sort) {
            final Sort s = (Sort)symb;
            addSort(s, l);
        }
        if (symb instanceof SortedOperator) {
            final SortedOperator s = (SortedOperator)symb;
            addSort(s.sort(), l);
        }
        if (symb instanceof Function) {
            final Function f = (Function)symb;
            addFunc(f, l);
        }
        if (symb instanceof ProgramVariable) {
            final ProgramVariable pv = (ProgramVariable)symb;
            addProgramVariable(pv, l);
        }
        if (symb instanceof SchemaVariable) {
            final SchemaVariable sv = (SchemaVariable)symb;
            addSchemaVariable(sv, l);
        }
        if (symb instanceof Taclet) {
            final Taclet t = (Taclet)symb;
            addTaclet(t, l);
        }
    }

    public void add(Term t) {
        assert t != null;
        t = TermBuilder.goBelowUpdates(t);
        if (!isPredicate(t.op())) {
            if (!t.subs().isEmpty()) {
                for (final Term s: t.subs()) {
                    add(s);
                }
            }
        }
        add(t.op());
    }

    public void addLabeled(Term t) {
        assert t != null;
        t = TermBuilder.goBelowUpdates(t);
        if (!t.subs().isEmpty()) {
            for (final Term s: t.subs()) {
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

    public void addTotalTerm(Term t) {
        assert t != null;
        if (t.op() instanceof UpdateApplication) {
            addTotalTerm(UpdateApplication.getUpdate(t));
            addTotalTerm(UpdateApplication.getTarget(t));
        }
        if (t.op() instanceof ElementaryUpdate) {
            add(((ElementaryUpdate)t.op()).lhs());
        }
        t = TermBuilder.goBelowUpdates(t);
        if (!t.subs().isEmpty()) {
            for (final Term s: t.subs()) {
                addTotalTerm(s);
            }
        }
        add(t.op());
    }

    public void addLabeledTotalTerm(Term t) {
        assert t != null;
        if (t.op() instanceof UpdateApplication) {
            addLabeledTotalTerm(UpdateApplication.getUpdate(t));
            addLabeledTotalTerm(UpdateApplication.getTarget(t));
        }
        if (t.op() instanceof ElementaryUpdate) {
            addLabeled(((ElementaryUpdate)t.op()).lhs());
        }
        t = TermBuilder.goBelowUpdates(t);
        if (!t.subs().isEmpty()) {
            for (final Term s: t.subs()) {
                addLabeledTotalTerm(s);
            }
        }
        addLabeled(t.op());
    }

    private ImmutableSet<Sort> getSorts() {
        ImmutableSet<Sort> sorts = DefaultImmutableSet.<Sort>nil();
        for (Pair<Sort, Boolean> s: this.sorts) {
            sorts = sorts.add(s.first);
        }
        return sorts;
    }

    private LinkedList<Sort> ensureRightOrderOfSorts(ImmutableSet<Sort> s){
        LinkedList<TreeSet<Sort>> sortContainers = new LinkedList<TreeSet<Sort>>();
        for (final Sort sort: s) {
            boolean added = false;
            for (TreeSet<Sort> container : sortContainers) {
                if (container.add(sort)) {
                    added = true;
                    break;
                }
            }
            if (!added) {
                sortContainers.add(new TreeSet<Sort>(new Comparator<Sort>() {

                    @Override
                    public int compare(Sort s1, Sort s2) {
                        if (s1.extendsTrans(s2)) {
                            return 1;
                        }
                        if (s2.extendsTrans(s1)) {
                            return -1;
                        }
                        return 0;
                    }
                }));
                sortContainers.getLast().add(sort);
            }
        }
        LinkedList<Sort> sorts = new LinkedList<Sort>();
        for (final TreeSet<Sort> container : sortContainers) {
            sorts.addAll(container);
        }
        return sorts;
    }

    private LinkedList<Sort> removeArraySorts(LinkedList<Sort> sorts){
        Iterator<Sort> it = sorts.iterator();
        while (it.hasNext()) {
            Sort s = it.next();
            if (s instanceof ArraySort) {
                it.remove();
            }
        }
        return sorts;
    }

    private ImmutableSet<Function> getPredicates() {
        ImmutableSet<Function> predicates = DefaultImmutableSet.<Function>nil();
        for (Pair<Function, Boolean> p: this.predicates) {
            predicates = predicates.add(p.first);
        }
        return predicates;
    }

    private ImmutableSet<Function> getFunctions() {
        ImmutableSet<Function> functions = DefaultImmutableSet.<Function>nil();
        for (Pair<Function, Boolean> f: this.functions) {
            functions = functions.add(f.first);
        }
        return functions;
    }

    private ImmutableSet<ProgramVariable> getProgramVariables() {
        ImmutableSet<ProgramVariable> programVariables = DefaultImmutableSet.<ProgramVariable>nil();
        for (Pair<ProgramVariable, Boolean> pv: this.programVariables) {
            programVariables = programVariables.add(pv.first);
        }
        return programVariables;
    }

    private ImmutableSet<SchemaVariable> getSchemaVariables() {
        ImmutableSet<SchemaVariable> schemaVariables = DefaultImmutableSet.<SchemaVariable>nil();
        for (Pair<SchemaVariable, Boolean> sv: this.schemaVariables) {
            schemaVariables = schemaVariables.add(sv.first);
        }
        return schemaVariables;
    }

    private ImmutableSet<Taclet> getTaclets() {
        ImmutableSet<Taclet> taclets = DefaultImmutableSet.<Taclet>nil();
        for (Pair<Taclet, Boolean> t: this.taclets) {
            taclets = taclets.add(t.first);
        }
        return taclets;
    }

    private String printSpace() {
        StringBuffer result = new StringBuffer();
        result.append("\n\n");
        return result.toString();
    }

    private String printSorts() {
        if (getSorts().isEmpty()) {
            return "";
        }

        StringBuffer result = new StringBuffer();
        result.append("\\sorts{\n");
        LinkedList<Sort> sortsList = ensureRightOrderOfSorts(getSorts());
        // bugfix (CS): array types need not to be added as sorts
        // (and they cannot be parsed...)
        sortsList = removeArraySorts(sortsList);
        for (final Sort sort: sortsList) {
            result.append(sort.name());
            if (!sort.extendsSorts().isEmpty()) {
                String res = "\\extends ";
                boolean extendsAtLeastOneSort = false;
                for (final Sort sortParent : sort.extendsSorts()) {
                    if (sortParent != Sort.ANY) {
                        res += sortParent.name() + ", ";
                        extendsAtLeastOneSort = true;
                    }
                }
                if (extendsAtLeastOneSort) {
                    final int index = res.lastIndexOf(", ");
                    res = res.substring(0,index == -1 ? res.length() : index);
                    result.append(res);
                }
            }
            result.append(";\n");
        }
        result.append("}\n\n");
        return result.toString();
    }

    private String printPredicates() {
        if (getPredicates().isEmpty()) {
            return "";
        }

        StringBuffer result = new StringBuffer();
        result.append("\\predicates{\n");
        for (final Function pred: getPredicates()) {
            result.append(pred.name());
            String s = "";
            for (int i = 0; i < pred.arity(); i++) {
                s+= (i == 0 ? "(" : ",");
                s+= (pred.argSort(i));
                s+= (i == pred.arity() - 1 ? ")" : "");
            }
            result.append(s);
            result.append(";\n");
        }
        result.append("}\n\n");
        return result.toString();
    }

    private String printFunctions() {
        if (getFunctions().isEmpty()) {
            return "";
        }

        StringBuffer result = new StringBuffer();
        result.append("\\functions{\n");
        for (final Function f: getFunctions()) {
            result.append(f.sort().name() + " ");
            result.append(f.name());
            String s = "";
            for (int i = 0; i < f.arity(); i++) {
                s+= (i == 0 ? "(" : ",");
                s+= (f.argSort(i));
                s+= (i == f.arity() - 1 ? ")" : "");
            }
            result.append(s);
            result.append(";\n");
        }
        result.append("}\n\n");
        return result.toString();
    }

    private String printProgramVariables() {
        if (getProgramVariables().isEmpty()) {
            return "";
        }

        StringBuffer result = new StringBuffer();
        result.append("\\programVariables{\n");
        for (final ProgramVariable pv: getProgramVariables()) {
            result.append(pv.sort().name() + " ");
            result.append(pv.name());
            result.append(";\n");
        }
        result.append("}\n\n");
        return result.toString();
    }

    @SuppressWarnings("unused")
    private String printSchemaVariables() {
        if (getSchemaVariables().isEmpty()) {
            return "";
        }

        StringBuffer result = new StringBuffer();
        result.append("\\schemaVariables{\n");
        for (final SchemaVariable sv: getSchemaVariables()) {
            final String prefix = sv instanceof FormulaSV ? "\\formula " :
                sv instanceof TermSV? "\\term " : "\\variables ";
            result.append(prefix);
            result.append(sv.sort().name() + " ");
            result.append(sv.name());
            result.append(";\n");
        }
        result.append("}\n\n");
        return result.toString();
    }

    private String printTaclets() {
        if (getTaclets().isEmpty()) {
            return "";
        }

        NotationInfo info = new NotationInfo();
        StringBackend backend = new StringBackend(80);
        LogicPrinter printer = new LogicPrinter(new ProgramPrinter(),info, backend,null,true);
        StringBuffer buffer = new StringBuffer();

        buffer.append("\\rules{");
        for (final Taclet taclet : getTaclets()) {
            buffer.append("\n\n");

            info = new NotationInfo();
            backend = new StringBackend(80);
            printer = new LogicPrinter(new ProgramPrinter(),info, backend,null,true);
            printer.printTaclet(taclet);
            final StringBuffer t = new StringBuffer(backend.getString()+";");
            buffer.append(t);
        }
        buffer.append("\n}");
        String string = buffer.toString();
        // bugfix (CS): the following two lines changed array types to their
        // base type -- which is no good idea. Thus I removed the lines.
//        string = string.replaceAll("\\[", "");
//        string = string.replaceAll("\\]", "");
        buffer = new StringBuffer();
        buffer.append(string);
        buffer.append("\n\n");
        return buffer.toString();
    }

    public String printProofSymbols() {
        StringBuffer result = new StringBuffer();

        result.append(printSpace());
        result.append(printSorts());
        result.append(printPredicates());
        result.append(printFunctions());
        result.append(printProgramVariables());
        //result.append(printSchemaVariables());
        result.append(printTaclets());

        return result.toString();
    }
}