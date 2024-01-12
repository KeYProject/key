/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.io.IOException;
import java.io.StringReader;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Properties;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.smt.newsmt2.MasterHandler.SymbolIntroducer;
import de.uka.ilkd.key.smt.newsmt2.SExpr.Type;
import de.uka.ilkd.key.smt.newsmt2.SMTHandlerProperty.BooleanProperty;

import static de.uka.ilkd.key.smt.newsmt2.SExpr.Type.BOOL;
import static de.uka.ilkd.key.smt.newsmt2.SExpr.Type.UNIVERSE;

/**
 * This handler is meant to translate all function symbols for which key axioms, SMT axioms or
 * defining taclets have been registered.
 *
 * <h2>Adding new function symbols</h2>
 *
 * New functions can be registered in a file {@code XXX.DefinedSymbolsHandler.preamble.xml} for some
 * prefix {@code XXX}. This file must be located in the resources for the package in which this
 * class resides.
 *
 * <p>
 * Such an xml file is not an actual xml file but rather an xml fragment consisting of a set of
 * entries to be used as axiomatisation when the SMT translation is triggered.
 *
 * Three kind of entries are possible for a function symbol f:
 * <ol>
 * <li><tt>f.axioms</tt>: Specify SMTLib code that will be added as an assertion to the resulting
 * SMT code. This cannot be checked for correctness, however</li>
 * <li><tt>f.taclets</tt>: Specify a (comma-separated) list of builtin KeY taclets whose meaning
 * formula will be translated as axiomatisation. Since the taclets are available in KeY, the
 * translation is as correct as the KeY calculus in this point.</li>
 * <li><tt>f.dl</tt>: Specify a DL formula to specify an axiom. The formula will be translated to
 * SMTLib and used as axiomatisation. There is a test case in the testing framework that requires
 * that all such axiomatisation is proved within KeY. If more than one DL axiom is required, the
 * next ones are called <tt>f.dl.2</tt>, <tt>f.dl.3</tt>, etc.</li>
 * </ol>
 *
 * <h2>Triggers in DL formulae</h2>
 *
 * When specifying DL formulae, you can use the {@code <<Trigger>>} term label to specify the
 * subterm which should be used as a trigger (:pattern) in SMTLib to help Z3 (and other solvers) to
 * instantiate the quantified variables suitably.
 *
 * <pre>
 *     \forall Seq s; seqLen(s)&lt;&lt;Trigger&gt;&gt; &gt;= 0
 * </pre>
 *
 * is the axiom for seqLen (hence stored in <tt>seqLen.dl</tt>). The trigger pattern to be used for
 * instantiation is <tt>seqLen(s)</tt> matching against any ground instance of seqLen.
 */
public class DefinedSymbolsHandler implements SMTHandler {

    public static final String PREFIX = "k_";
    private static final String AXIOMS_SUFFIX = ".axioms";
    private static final String DL_SUFFIX = ".dl";
    private static final String TACLETS_SUFFIX = ".taclets";
    private static final String DECLS_SUFFIX = ".decls";
    private static final String TYPING_SUFFIX = ".typing";
    private static final Set<String> SUPPORTED_SUFFIXES =
        new HashSet<>(Arrays.asList(AXIOMS_SUFFIX, DL_SUFFIX, TACLETS_SUFFIX));
    private static final SMTHandlerProperty.BooleanProperty PROPERTY_AXIOMATISATION =
        new BooleanProperty("Axiomatisations", "Exclude axiomatisations",
            "SMT axioms may be present for symbols and included in the translation. "
                + "These axioms make the translation more powerful, but may also lead the "
                + "solver astray.");

    private final Set<String> supportedFunctions = new HashSet<>();
    private Services services;

    public static final TermLabel TRIGGER_LABEL = new ParameterlessTermLabel(new Name("Trigger"));

    private Properties snippets;
    private boolean enabled;

    @Override
    public void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) throws IOException {
        this.services = services;
        this.snippets = handlerSnippets;

        // extract the list of supported suffixes from the keys in the
        // properties.
        for (String prop : handlerSnippets.stringPropertyNames()) {
            int dot = prop.lastIndexOf('.');
            if (dot < 0) {
                continue;
            }
            String ext = prop.substring(dot);
            SymbolIntroducer introduceSymbol = this::introduceSymbol;
            if (SUPPORTED_SUFFIXES.contains(ext)) {
                String fct = prop.substring(0, dot);
                supportedFunctions.add(fct);
                masterHandler.getTranslationState().put(fct + ".intro", introduceSymbol);
            }
        }

        this.enabled = PROPERTY_AXIOMATISATION.get(masterHandler.getTranslationState());
    }


    @Override
    public boolean canHandle(Operator op) {
        return op instanceof Function && supportedFunctions.contains(op.name().toString());
    }

    private void introduceSymbol(MasterHandler trans, String name) throws SMTTranslationException {
        introduceSymbol(trans, name, services.getNamespaces().functions().lookup(name));
    }

    private boolean introduceSymbol(MasterHandler trans, String name, SortedOperator op)
            throws SMTTranslationException {
        if (trans.isKnownSymbol(name)) {
            return true;
        }

        // Now ... this is the first encounter of name.
        // We have to add axioms and typing and declaration ...

        String prefixedname = PREFIX + name;

        // Lookup a declaration in the snippets or use default if not present
        Writable decls;
        if (snippets.containsKey(name + DECLS_SUFFIX)) {
            decls = new VerbatimSMT(snippets.getProperty(name + DECLS_SUFFIX));
        } else {
            decls = HandlerUtil.funDeclaration(op, prefixedname);
        }
        trans.addDeclaration(decls);

        if (op.sort() != Sort.FORMULA) {
            // Lookup a typing axiom in the snippets or use default if not present
            Writable typing;
            if (snippets.contains(name + TYPING_SUFFIX)) {
                typing = new VerbatimSMT(name + TYPING_SUFFIX);
            } else {
                typing = HandlerUtil.funTypeAxiom(op, prefixedname, trans);
            }
            trans.addAxiom(typing);
        }

        trans.addKnownSymbol(name);

        // Add the axioms from the various possible sources. ...
        if (snippets.containsKey(name + AXIOMS_SUFFIX)) {
            handleSMTAxioms(trans, name);
            return true;
        }

        if (snippets.containsKey(name + DL_SUFFIX)) {
            handleDLAxioms(name, trans);
            return true;
        }

        if (snippets.containsKey(name + TACLETS_SUFFIX)) {
            // handle taclets
            handleTacletAxioms(name, trans);
            return true;
        }

        return false;
    }

    @Override
    public SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException {
        SortedOperator op = (SortedOperator) term.op();
        String name = op.name().toString();
        String prefixedname = PREFIX + name;

        List<SExpr> children = trans.translate(term.subs(), Type.UNIVERSE);
        SExpr.Type exprType = term.sort() == Sort.FORMULA ? BOOL : UNIVERSE;
        SExpr result = new SExpr(prefixedname, exprType, children);

        if (!introduceSymbol(trans, name, op)) {
            throw new SMTTranslationException(
                "I thought I would handle this term, but cannot: " + term);
        }

        return result;
    }

    @Override
    public List<SMTHandlerProperty<?>> getProperties() {
        return List.of(PROPERTY_AXIOMATISATION);
    }

    private void handleTacletAxioms(String name, MasterHandler trans)
            throws SMTTranslationException {
        String[] strTaclets = snippets.getProperty(name + TACLETS_SUFFIX).trim().split(" *, *");
        for (String str : strTaclets) {
            Taclet taclet = services.getProof().getInitConfig().lookupActiveTaclet(new Name(str));
            if (taclet == null) {
                throw new SMTTranslationException("Unknown taclet: " + str);
            }
            SMTTacletTranslator tacletTranslator = new SMTTacletTranslator(services);
            Term formula = tacletTranslator.translate(taclet);
            SExpr smt = trans.translate(formula);
            trans.addAxiom(SExprs.assertion(smt));
        }
    }

    private void handleSMTAxioms(MasterHandler trans, String name) throws SMTTranslationException {
        // well ... if that is defined by axioms use the general purpose mechanism.
        String axioms = snippets.getProperty(name + AXIOMS_SUFFIX);
        trans.addAxiom(new VerbatimSMT(axioms));
        String[] deps = snippets.getProperty(name + ".deps", "").trim().split(", *");
        for (String dep : deps) {
            trans.introduceSymbol(dep);
        }
    }

    private void handleDLAxioms(String name, MasterHandler trans) throws SMTTranslationException {
        int cnt = 2;
        String snipName = name + DL_SUFFIX;
        String dl = snippets.getProperty(snipName);
        do {
            DefaultTermParser tp = new DefaultTermParser();
            try {
                NamespaceSet nss = services.getNamespaces().copy();
                Services localServices = services.getOverlay(nss);
                // The parser may add new symbols (instantiations of sort-dep symbols).
                // Since the SMT machines run in parallel, this may cause
                // ConcurrentModificationExceptions. To avoid such exceptions,
                // a wrapper services object is used.
                Term axiom = tp.parse(new StringReader(dl), Sort.FORMULA, localServices, nss,
                    new AbbrevMap());
                trans.addAxiom(SExprs.assertion(trans.translate(axiom)));
            } catch (ParserException e) {
                throw new SMTTranslationException("Error while translating snippet " + snipName, e);
            }
            snipName = name + DL_SUFFIX + "." + cnt;
            dl = snippets.getProperty(snipName);
            cnt++;
        } while (dl != null);
    }

}
