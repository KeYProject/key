package de.uka.ilkd.key.proof.init;

import java.util.Comparator;
import java.util.LinkedList;
import java.util.TreeSet;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.pp.StringBackend;

public class InfFlowProofSymbols {

    private ImmutableSet<Sort> sorts
            = DefaultImmutableSet.<Sort>nil();

    private ImmutableSet<Function> predicates
            = DefaultImmutableSet.<Function>nil();

    private ImmutableSet<Function> functions
            = DefaultImmutableSet.<Function>nil();

    private ImmutableSet<ProgramVariable> programVariables
            = DefaultImmutableSet.<ProgramVariable>nil();

    private ImmutableSet<SchemaVariable> schemaVariables
            = DefaultImmutableSet.<SchemaVariable>nil();

    private ImmutableSet<Taclet> taclets
            = DefaultImmutableSet.<Taclet>nil();

    public InfFlowProofSymbols() {
    }

    private void addTerm(Term t) {
        if (!t.subs().isEmpty()) {
            for (final Term s: t.subs()) {
                addTerm(s);
            }
        }
        add(t.op());
    }

    private void addTaclet(Taclet t) {
        assert t != null;
        if (!taclets.contains(t)) {
            taclets = taclets.add(t);
        }
    }

    private void addSort(Sort s) {
        assert s != null;
        if (!(s instanceof NullSort) &&
                !sorts.contains(s)) {
            sorts = sorts.add(s);
        }
    }

    private void addFunction(Function f) {
        assert f != null;
        if (!functions.contains(f) &&
                !predicates.contains(f)) {
            if (f.name().toString().startsWith("RELATED_BY") ||
                    f.name().toString().startsWith("EXECUTION_OF")) {
                predicates = predicates.add(f);
            } else {
                functions = functions.add(f);
            }
        }
    }

    private void addSchemaVariable(SchemaVariable sv) {
        assert sv != null;
        if (!schemaVariables.contains(sv)) {
            schemaVariables = schemaVariables.add(sv);
        }
    }

    private void addProgramVariable(ProgramVariable pv) {
        assert pv != null;
        if (!programVariables.contains(pv)) {
            programVariables = programVariables.add(pv);
        }
    }

    public void add(Object symb) {
        assert symb != null;
        if (symb instanceof Term) {
            final Term t = (Term)symb;
            addTerm(t);
        }
        if (symb instanceof Sort) {
            final Sort s = (Sort)symb;
            addSort(s);
        }
        if (symb instanceof SortedOperator) {
            final SortedOperator s = (SortedOperator)symb;
            addSort(s.sort());
        }
        if (symb instanceof Function) {
            final Function f = (Function)symb;
            addFunction(f);
        }
        if (symb instanceof ProgramVariable) {
            final ProgramVariable pv = (ProgramVariable)symb;
            addProgramVariable(pv);
        }
        if (symb instanceof SchemaVariable) {
            final SchemaVariable sv = (SchemaVariable)symb;
            addSchemaVariable(sv);
        }
        if (symb instanceof Taclet) {
            final Taclet t = (Taclet)symb;
            addTaclet(t);
        }
    }

    public void add(ImmutableList<?> symbs) {
        assert symbs != null;
        for (final Object symb: symbs) {
            add(symb);
        }
    }

    private ImmutableSet<Sort> getSorts() {
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

    private ImmutableSet<Function> getPredicates() {
        return predicates;
    }

    private ImmutableSet<Function> getFunctions() {
        return functions;
    }

    private ImmutableSet<ProgramVariable> getProgramVariables() {
        return programVariables;
    }

    private ImmutableSet<SchemaVariable> getSchemaVariables() {
        return schemaVariables;
    }

    private ImmutableSet<Taclet> getTaclets() {
        ImmutableSet<Taclet> res = DefaultImmutableSet.<Taclet>nil();
        for (final Taclet t: taclets) {
            res = res.add(t);
        }
        return res;
    }

    private String printSorts() {
        if (getSorts().isEmpty()) {
            return "";
        }

        StringBuffer result = new StringBuffer();
        result.append("\n\n\\sorts{\n");
        final LinkedList<Sort> sorts = ensureRightOrderOfSorts(getSorts());
        for (final Sort sort: sorts) {
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
        return result.toString();
    }

    private String printPredicates() {
        if (getPredicates().isEmpty()) {
            return "";
        }

        StringBuffer result = new StringBuffer();
        result.append("}\n\n\\predicates{\n");
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
        return result.toString();
    }

    private String printFunctions() {
        if (getFunctions().isEmpty()) {
            return "";
        }

        StringBuffer result = new StringBuffer();
        result.append("}\n\n\\functions{\n");
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
        return result.toString();
    }

    private String printProgramVariables() {
        if (getProgramVariables().isEmpty()) {
            return "";
        }

        StringBuffer result = new StringBuffer();
        result.append("}\n\n\\programVariables{\n");
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
        string = string.replaceAll("\\[", "");
        string = string.replaceAll("\\]", "");
        buffer = new StringBuffer();
        buffer.append(string);
        buffer.append("\n\n");
        return buffer.toString();
    }

    public String printProofSymbols() {
        StringBuffer result = new StringBuffer();

        result.append(printSorts());
        result.append(printPredicates());
        result.append(printFunctions());
        result.append(printProgramVariables());
        //result.append(printSchemaVariables());
        result.append(printTaclets());

        return result.toString();
    }
}