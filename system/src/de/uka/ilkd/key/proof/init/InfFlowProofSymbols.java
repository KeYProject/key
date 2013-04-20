package de.uka.ilkd.key.proof.init;

import java.util.Comparator;
import java.util.LinkedList;
import java.util.TreeSet;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Named;
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
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.pp.StringBackend;

public class InfFlowProofSymbols {

    private ImmutableSet<Sort> sorts
        = DefaultImmutableSet.<Sort>nil();

    private ImmutableSet<Function> functions
        = DefaultImmutableSet.<Function>nil();

    private ImmutableSet<SchemaVariable> schemaVariables
        = DefaultImmutableSet.<SchemaVariable>nil();

    private ImmutableSet<ProgramVariable> programVariables
    = DefaultImmutableSet.<ProgramVariable>nil();

    private ImmutableSet<Function> predicates
        = DefaultImmutableSet.<Function>nil();

    private ImmutableSet<NoPosTacletApp> taclets
        = DefaultImmutableSet.<NoPosTacletApp>nil();

    public InfFlowProofSymbols() {
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
            functions = functions.add(f);
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

    public void addPredicate(Function p) {
        assert p != null;
        if (!predicates.contains(p)) {
            predicates = predicates.add(p);
        }
    }

    private void addSymbol(Named symb) {
        assert symb != null;
        if (symb instanceof Sort) {
            Sort s = (Sort)symb;
            addSort(s);
        }
        if (symb instanceof Function) {
            Function f = (Function)symb;
            addFunction(f);
        }
        if (symb instanceof SchemaVariable) {
            SchemaVariable sv = (SchemaVariable)symb;
            addSchemaVariable(sv);
        }
        if (symb instanceof ProgramVariable) {
            ProgramVariable pv = (ProgramVariable)symb;
            addProgramVariable(pv);
        }
        if (symb instanceof SortedOperator) {
            SortedOperator s = (SortedOperator)symb;
            addSort(s.sort());
        }
    }

    public void addSymbols(ImmutableList<Named> ss) {
        for (Named s: ss) {
            addSymbol(s);
        }
    }

    public void addTerm(Term t) {
        if (!t.subs().isEmpty()) {
            for (Term s: t.subs()) {
                addTerm(s);
            }
        }
        addSymbol(t.op());
    }

    public void addTerms(ImmutableList<Term> ts) {
        for (Term t: ts) {
            addTerm(t);
        }
    }

    private ImmutableSet<Sort> getSorts() {
        return sorts;
    }

    private LinkedList<Sort> ensureRightOrderOfSorts(ImmutableSet<Sort> s){
        LinkedList<TreeSet<Sort>> sortContainers = new LinkedList<TreeSet<Sort>>();
        for (Sort sort: s) {
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
        for (TreeSet<Sort> container : sortContainers) {
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

    public void addTaclet(Taclet t, Services services) {
        assert t != null;
        if (!getTaclets().contains(t)) {
            NoPosTacletApp app = NoPosTacletApp
                    .createFixedNoPosTacletApp(t,
                                               SVInstantiations.EMPTY_SVINSTANTIATIONS,
                                               services);
            taclets = taclets.add(app);
        }
    }

    private ImmutableSet<Taclet> getTaclets() {
        ImmutableSet<Taclet> res = DefaultImmutableSet.<Taclet>nil();
        for (NoPosTacletApp t: taclets) {
            res = res.add(t.taclet());
        }
        return res;
    }

    private String printSorts() {
        if (getSorts().isEmpty()) {
            return "";
        }

        StringBuffer result = new StringBuffer();
        result.append("\n\n\\sorts{\n");
        LinkedList<Sort> sorts = ensureRightOrderOfSorts(getSorts());
        for (Sort sort: sorts) {
            result.append(sort.name());
            if (!sort.extendsSorts().isEmpty()) {
                String res = "\\extends ";
                boolean extendsAtLeastOneSort = false;
                for (Sort sortParent : sort.extendsSorts()) {
                    if (sortParent != Sort.ANY) {
                        res += sortParent.name() + ", ";
                        extendsAtLeastOneSort = true;
                    }
                }
                if (extendsAtLeastOneSort) {
                    int index = res.lastIndexOf(", ");
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
        for (Function pred: getPredicates()) {
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
        for (Function f: getFunctions()) {
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
        for (ProgramVariable pv: getProgramVariables()) {
            result.append(pv.sort().name() + " ");
            result.append(pv.name());
            result.append(";\n");
        }
        result.append("}\n\n");
        return result.toString();
    }

    private String printSchemaVariables() {
        if (getSchemaVariables().isEmpty()) {
            return "";
        }

        StringBuffer result = new StringBuffer();
        result.append("\\schemaVariables{\n");
        for (SchemaVariable sv: getSchemaVariables()) {
            String prefix = sv instanceof FormulaSV ? "\\formula " :
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
        for (Taclet taclet : getTaclets()) {
            buffer.append("\n\n");

            info = new NotationInfo();
            backend = new StringBackend(80);
            printer = new LogicPrinter(new ProgramPrinter(),info, backend,null,true);
            printer.printTaclet(taclet);
            StringBuffer t = new StringBuffer(backend.getString()+";");
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

    public String printProofSymbols() { // TODO: Might need some improvement
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