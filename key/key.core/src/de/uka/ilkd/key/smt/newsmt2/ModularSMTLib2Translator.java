package de.uka.ilkd.key.smt.newsmt2;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.smt.IllegalFormulaException;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.smt.SMTTranslator;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;

public class ModularSMTLib2Translator implements SMTTranslator {

    public static final String SORT_PREFIX = "sort_";

    private static final String PREAMBLE = readPreamble();

    private List<Throwable> exceptions = Collections.emptyList();

    @Override
    public StringBuffer translateProblem(Term problem, Services services, SMTSettings settings)
            throws IllegalFormulaException {

        MasterHandler master = new MasterHandler(services);

        SExpr result = master.translate(problem, Type.BOOL);
        exceptions = master.getExceptions();

        postProcess(result);

        StringBuffer sb = new StringBuffer();

        sb.append("; --- Preamble\n\n");
        sb.append(PREAMBLE);

        sb.append("; --- Declarations\n\n");

        StringBuffer sortsb = new StringBuffer();
        sortsb.append("(distinct ");
        for (Sort s : services.getNamespaces().sorts().elements()) {
            sb.append("(declare-const " + SExpr.sortExpr(s) + " T)\n");
            sortsb.append(SExpr.sortExpr(s) + " ");
        }
        sortsb.append(")\n");
        sb.append(sortsb);
        sb.append("\n");
        for(SExpr decl : master.getDeclarations()) {
            decl.appendTo(sb);
            sb.append("\n");
        }

        sb.append("; --- Axioms\n\n");
        for (SExpr ax : master.getAxioms()) {
            ax.appendTo(sb);
            sb.append("\n\n");
        }

        sb.append("; --- Sequent\n\n");
        SExpr assertion = new SExpr("assert", Type.NONE, result);
        assertion.appendTo(sb);

        return sb;
    }


    // Is there functionality to do this in KeY ?!
    private static String readPreamble() {
        BufferedReader r = new BufferedReader(
                new InputStreamReader(
                        ModularSMTLib2Translator.class.getResourceAsStream("preamble.smt2")));

        try {
            String line;
            StringBuilder sb = new StringBuilder();
            while((line = r.readLine()) != null) {
                sb.append(line).append("\n");
            }

            return sb.toString();
        } catch (IOException e) {
            return ";;;; CANNOT READ PREAMBLE";
        }
    }


    private void postProcess(SExpr result) {
        // TODO: remove (u2i (i2u x)) --->  x
    }

    @Override
    public Collection<Throwable> getExceptionsOfTacletTranslation() {
        return exceptions;
    }

}
