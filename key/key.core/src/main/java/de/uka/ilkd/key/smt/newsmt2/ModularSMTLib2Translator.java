package de.uka.ilkd.key.smt.newsmt2;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.IllegalFormulaException;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.smt.SMTTranslator;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

/*
    This class provides a translation from a KeY sequent to the SMT-LIB 2 language,
    a common input language for modern SMT solvers. It aims to be modular and therefore
    easily extendable. Special handlers are used for different terms. New handlers need
    to be registered in the file "de.uka.ilkd.key.smt.newsmt2.SMTHandler" in the
    /key/key.core/src/main/resources/META-INF/services/ directory.
 */

public class ModularSMTLib2Translator implements SMTTranslator {

    static final String SORT_PREFIX = "sort_";

    private List<Throwable> exceptions = Collections.emptyList();

    private List<Throwable> tacletExceptions = Collections.emptyList();

    // REVIEW MU: Eventually switch to StringBuilder which is faster
    @Override
    public StringBuffer translateProblem(Term problem, Services services, SMTSettings settings) {

        MasterHandler master;
        try {
            master = new MasterHandler(services);
        } catch (IOException ex) {
            exceptions = Collections.singletonList(ex);
            // Review MU: This should not be reported as exceptions only ...
            return new StringBuffer("error while translating");
        }

        List<Term> sequentAsserts = smashProblem(problem, services);
        List<SExpr> results = new LinkedList<>();
        for (Term t : sequentAsserts) {
            results.add(master.translate(t, Type.BOOL));
        }

//        SExpr result = master.translate(problem, Type.BOOL);
        exceptions = master.getExceptions();

//        postProcess(result);

        StringBuffer sb = new StringBuffer();

        sb.append("; --- Preamble");
        for (Writable w : master.getOptions()) {
            w.appendTo(sb);
        }
        sb.append("\n(set-option :produce-proofs true)");

        sb.append("; --- Declarations");

        if (problem.arity() != 0) {
            master.addSort(Sort.ANY);
            addAllSorts(problem, master);
        }

        List<SExpr> sortExprs = new LinkedList<>();
        for (Sort s : master.getSorts()) {
            if (s != Sort.ANY && !(TypeManager.isSpecialSort(s))) {
                master.addDeclaration(new SExpr("declare-const", SExpr.sortExpr(s).toString(), "T"));
            }
            sortExprs.add(SExpr.sortExpr(s));
        }
        if (master.getSorts().size() > 1) {
            master.addDeclaration(new SExpr("assert", Type.BOOL,
                    new SExpr("distinct", Type.BOOL, sortExprs)));
        }
        sb.append("\n");

        TypeManager tm = new TypeManager();
        tm.createSortTypeHierarchy(master);

        for (Writable decl : master.getDeclarations()) {
            decl.appendTo(sb);
            sb.append("\n");
        }

        sb.append("\n; --- Axioms\n");
        for (Writable ax : master.getAxioms()) {
            ax.appendTo(sb);
            sb.append("\n");
        }

        sb.append("\n; --- Sequent\n");
        for (SExpr ass : results) {
            SExpr assertion = new SExpr("assert", ass);
            assertion.appendTo(sb);
            sb.append("\n");
        }

        sb.append("\n(check-sat)");
        sb.append("\n(get-proof)");

        sb.append("\n\n; --- Translation of unknown values\n");
        for (Term t : master.getUnknownValues().keySet()) {
            sb.append("; " + master.getUnknownValues().get(t).toString() + " :  " + t.toString() + "\n");
        }


        // any exceptions?
        for (Throwable t : exceptions) {
            sb.append("\n; " + t.toString());
        }

        return sb;
    }

    /**
     * Adds all sorts contained in the given problem to the master handler.
     * @param problem the given problem
     * @param master the master handler of the problem
     */
    // TODO js: expressions within updates are not found by this, which leads to failures.
    private void addAllSorts(Term problem, MasterHandler master) {
        Sort s = problem.sort();
        master.addSort(s);
        for (Term t : problem.subs()) {
            addAllSorts(t, master);
        }
    }

    private static String readResource(String s) {
        BufferedReader r = new BufferedReader(
                new InputStreamReader(
                        ModularSMTLib2Translator.class.getResourceAsStream(s)));

        try {
            String line;
            StringBuilder sb = new StringBuilder();
            while ((line = r.readLine()) != null) {
                sb.append(line).append("\n");
            }

            return sb.toString();
        } catch (IOException e) {
            return ";;;; CANNOT READ " + s;
        }
    }

    //just testing: break the top-level seq formula into single assertions
    private List<Term> smashProblem(Term problem, Services s) {
        TermBuilder tb = s.getTermBuilder();
        List<Term> res = new LinkedList<>();
        if (problem.op() == Junctor.IMP) {
            Term left = problem.sub(0);
            Term right = problem.sub(1);
            while (left.op() == Junctor.AND) {
                res.add(left.sub(1));
                left = left.sub(0);
            }
            res.add(left);
            while (right.op() == Junctor.OR) {
                res.add(tb.not(right.sub(1)));
                right = right.sub(0);
            }
            res.add(tb.not(right));
        } else { //TODO js make sure this includes all cases
            res.add(tb.not(problem));
        }
        return res;
    }

    private void postProcess(SExpr result) {
        // TODO: remove (u2i (i2u x)) --->  x
    }


    @Override
    public Collection<Throwable> getExceptionsOfTacletTranslation() {
        return tacletExceptions;
    }


    @Override
    public ArrayList<StringBuffer> translateTaclets(Services services, SMTSettings settings) throws IllegalFormulaException {
        // not yet implemented. maybe adapt the existing method from abstractsmttranslator
        return null;
    }

}
