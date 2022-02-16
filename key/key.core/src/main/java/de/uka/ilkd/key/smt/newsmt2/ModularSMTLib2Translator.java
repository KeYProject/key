package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.smt.SMTTranslator;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.LinkedList;
import java.util.List;

/**
 * This class provides a translation from a KeY sequent to the SMT-LIB 2 language, a common input
 * language for modern SMT solvers.
 *
 * It aims to be modular and therefore easily extendable. Special handlers are used for different
 * terms. New handlers need to be registered in the file "de.uka.ilkd.key.smt.newsmt2.SMTHandler" in
 * the /key/key.core/src/main/resources/META-INF/services/ directory.
 *
 * @author Jonas Schiffl
 * @author Mattias Ulbrich
 */
public class ModularSMTLib2Translator implements SMTTranslator {
    private static final Logger LOGGER = LoggerFactory.getLogger(ModularSMTLib2Translator.class);

    /** If there is a custom list of smt handlers, store them here */
    private final @Nullable List<SMTHandler> smtHandlers;

    public ModularSMTLib2Translator(List<SMTHandler> smtHandlers) {
        this.smtHandlers = smtHandlers;
    }

    public ModularSMTLib2Translator() {
        this.smtHandlers = null;
    }

    @Override
    public CharSequence translateProblem(Sequent sequent, Services services, SMTSettings settings) {

        MasterHandler master;
        try {
            master = new MasterHandler(services, settings, smtHandlers);
        } catch (IOException ex) {
            throw new RuntimeException(ex);
        }

        List<Term> sequentAsserts = getTermsFromSequent(sequent, services);
        List<SExpr> sequentSMTAsserts = makeSMTAsserts(master, sequentAsserts);

        StringBuilder sb = new StringBuilder();

        sb.append("; --- Preamble");
        sb.append(SMTHandlerServices.getInstance().getPreamble());

        sb.append("; --- Declarations\n");
        extractSortDeclarations(sequent, services, master, sequentAsserts);
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
        for (SExpr ass : sequentSMTAsserts) {
            SExpr assertion = new SExpr("assert", ass);
            assertion.appendTo(sb);
            sb.append("\n");
        }

        sb.append("\n(check-sat)");

        if(!master.getUnknownValues().isEmpty()) {
            sb.append("\n\n; --- Translation of unknown values\n");
            for (Term t : master.getUnknownValues().keySet()) {
                sb.append("; ")
                    .append(master.getUnknownValues().get(t).toString())
                    .append(" :  ")
                    .append(t.toString().replace("\n", "")).append("\n");
            }
        }

        // any exceptions?
        List<Throwable> exceptions = master.getExceptions();
        for (Throwable t : exceptions) {
            sb.append("\n; ").append(t.toString().replace("\n", "\n;"));
            t.printStackTrace();
        }

        // TODO Find a concept for exceptions here
        if(!exceptions.isEmpty()) {
            LOGGER.error("Exception while translating: {}", sb);
            throw new RuntimeException(exceptions.get(0));
        }

        return sb;
    }

    /*
     * precompute the information on the required sources from the translation.
     */
    private void extractSortDeclarations(Sequent sequent, Services services, MasterHandler master,
                                         List<Term> sequentAsserts) {
        TypeManager tm = new TypeManager(services);
        tm.handle(master);
    }

    /*
     * extract a sequent into an SMT collection.
     *
     * The translation adds elements to the lists in the master handler
     * on the way.
     */
    private List<SExpr> makeSMTAsserts(MasterHandler master, List<Term> sequentAsserts) {
        List<SExpr> sequentSMTAsserts = new LinkedList<>();
        for (Term t : sequentAsserts) {
            sequentSMTAsserts.add(master.translate(t, Type.BOOL));
        }
        return sequentSMTAsserts;
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

    /*
     * Turn a sequent to a collection of formulas. Antecedent positive, succedent negated.
     */
    private List<Term> getTermsFromSequent(Sequent seq, Services serv) {
        TermBuilder tb = serv.getTermBuilder();
        List<Term> res = new LinkedList<>();
        for (SequentFormula sf : seq.antecedent()) {
            res.add(sf.formula());
        }
        for (SequentFormula sf : seq.succedent()) {
            res.add(tb.not(sf.formula()));
        }
        return res;
    }

    /**
     * remove obvious identities from SMT code.
     *
     * @param result, a non-null SExpr
     * @return an equivalent smt code with some simplifications
     */
    private SExpr postProcess(SExpr result) {
        // remove (u2i (i2u x)) --->  x
        if(result.getName().equals("u2i") && result.getChildren().get(0).getName().equals("i2u")) {
            return postProcess(result.getChildren().get(0).getChildren().get(0));
        }

        // remove (u2b (b2u x)) --->  x
        if(result.getName().equals("u2b") && result.getChildren().get(0).getName().equals("b2u")) {
            return postProcess(result.getChildren().get(0).getChildren().get(0));
        }

        return result.map(this::postProcess);
    }

}
