/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import javax.annotation.Nullable;

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

/**
 * This class provides a translation from a KeY sequent to the SMT-LIB 2 language, a common input
 * language for modern SMT solvers.
 *
 * It aims to be modular and therefore easily extendable. Special {@link SMTHandler}s are used for
 * different terms. The class names of the desired handlers have to be given to the constructor.
 *
 * @author Jonas Schiffl
 * @author Mattias Ulbrich
 */
public class ModularSMTLib2Translator implements SMTTranslator {
    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(ModularSMTLib2Translator.class);

    /**
     * Handler option. If provided, the translator will label translations of sequent formulas such
     * that {@link de.uka.ilkd.key.gui.smt.SMTFocusResults} can interpret the unsat core.
     * <p>
     * This option is currently only enabled for Z3.
     * Currently, this option only works with a CVC5 dev build.
     * Once <a href="https://github.com/cvc5/cvc5/pull/9353">the fix</a> is included in a release,
     * add this handler option to the .props file.
     * </p>
     * Make sure to also send (get-unsat-core) in the respective socket class when adding this
     * option.
     */
    private static final String GET_UNSAT_CORE = "getUnsatCore";

    /**
     * The smt preamble prepended to smt problems that are created with this translator.
     */
    private final String preamble;
    /**
     * The fully classified class names of the SMTHandlers used by this translator.
     */
    private final String[] handlerNames;
    /**
     * Arbitrary String options for the SMTHandlers used by this translator.
     */
    private final String[] handlerOptions;

    /**
     * Customizable preamble and {@link SMTHandler} list for this Translator to use instead of the
     * default values.
     *
     * @param preamble the preamble to be prepended to smt problems created with this translator
     * @param handlerOptions arbitrary String options for the SMTHandlers used by this translator
     * @param handlerNames fully classified class names of the SMTHandlers to be used by this
     *        translator
     */
    public ModularSMTLib2Translator(String[] handlerNames, String[] handlerOptions,
            @Nullable String preamble) {
        if (preamble == null) {
            this.preamble = SMTHandlerServices.getInstance().getPreamble();
        } else {
            this.preamble = preamble;
        }
        this.handlerNames = handlerNames;
        this.handlerOptions = handlerOptions;
        /*
         * Make sure to load the needed handlers once so that their smt properties are loaded as
         * well. This is needed so that the properties already exist before first translating
         * anything as they may have settings that should be visible beforehand (see {@link
         * SMTSettingsProvider). Also, loading them once before the first translation may save
         * runtime for that first translation.
         */
        try {
            SMTHandlerServices.getInstance().getTemplateHandlers(handlerNames);
        } catch (IOException e) {
            LOGGER.warn(e.getMessage());
        }
    }

    /**
     * If the preamble and handlers don't have to be customized, the handlers are empty and the
     * preamble may be the one from {@link SMTHandlerServices#getPreamble()}.
     */
    public ModularSMTLib2Translator() {
        this(new String[0], new String[0], null);
    }

    @Override
    public CharSequence translateProblem(Sequent sequent, Services services, SMTSettings settings) {

        MasterHandler master;
        try {
            master = new MasterHandler(services, settings, handlerNames, handlerOptions);
        } catch (IOException ex) {
            throw new RuntimeException(ex);
        }

        List<Term> sequentAsserts = getTermsFromSequent(sequent, services);
        List<SExpr> sequentSMTAsserts = makeSMTAsserts(master, sequentAsserts);

        StringBuilder sb = new StringBuilder();

        sb.append("; --- Preamble\n");
        sb.append(preamble);
        sb.append(System.lineSeparator());

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

        boolean getUnsatCore = Arrays.asList(handlerOptions).contains(GET_UNSAT_CORE);
        sb.append("\n; --- Sequent\n");
        int i = 1;
        for (SExpr ass : sequentSMTAsserts) {
            if (getUnsatCore) {
                String label = "L_" + i;
                i++;
                ass = SExprs.named(ass, label);
            }
            SExpr assertion = new SExpr("assert", ass);
            assertion.appendTo(sb);
            sb.append("\n");
        }

        sb.append("\n(check-sat)");

        if (!master.getUnknownValues().isEmpty()) {
            sb.append("\n\n; --- Translation of unknown values\n");
            for (Term t : master.getUnknownValues().keySet()) {
                sb.append("; ").append(master.getUnknownValues().get(t).toString()).append(" :  ")
                        .append(t.toString().replace("\n", "")).append("\n");
            }
        }

        // any exceptions?
        List<Throwable> exceptions = master.getExceptions();
        for (Throwable t : exceptions) {
            sb.append("\n; ").append(t.toString().replace("\n", "\n;"));
            LOGGER.warn("Exception", t);
        }

        // TODO Find a concept for exceptions here
        if (!exceptions.isEmpty()) {
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
     * The translation adds elements to the lists in the master handler on the way.
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
            new InputStreamReader(ModularSMTLib2Translator.class.getResourceAsStream(s),
                StandardCharsets.UTF_8));

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
        // remove (u2i (i2u x)) ---> x
        if (result.getName().equals("u2i") && result.getChildren().get(0).getName().equals("i2u")) {
            return postProcess(result.getChildren().get(0).getChildren().get(0));
        }

        // remove (u2b (b2u x)) ---> x
        if (result.getName().equals("u2b") && result.getChildren().get(0).getName().equals("b2u")) {
            return postProcess(result.getChildren().get(0).getChildren().get(0));
        }

        return result.map(this::postProcess);
    }

}
