/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.Collection;

import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortedOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.TacletFormula;
import de.uka.ilkd.key.taclettranslation.TacletVisitor;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.LoaderListener;

import org.key_project.util.collection.ImmutableSet;


/**
 * Creates for a given set of taclets the corresponding set of proof obligation. For more
 * information see public method <code>create(...)</code>.
 *
 */
public class ProofObligationCreator {

    private String createName(ProofAggregate[] singleProofs) {
        return "Side proofs for " + singleProofs.length + " taclets.";
    }


    /**
     * Creates for each taclet in <code>taclets</code> a proof obligation containing the
     * corresponding FOL formula of the taclet.
     *
     * @param taclets Sets of taclets the proof obligations should be created for.
     * @param initConfigs the initial configuration that should be used for creating the proofs.
     * @param axioms The set of user-defined taclets that should be used as additional rules. This
     *        taclets are added to the single proof obligation so that they can be used for the
     *        proof.
     * @param listeners a listener that observes the single steps. Used for status information.
     * @return A proof aggregate containing the proofs created by this method.
     */
    public ProofAggregate create(ImmutableSet<Taclet> taclets, InitConfig[] initConfigs,
            ImmutableSet<Taclet> axioms, Collection<LoaderListener> listeners) {

        ProofAggregate[] singleProofs = new ProofAggregate[taclets.size()];

        for (LoaderListener listener : listeners) {
            listener.progressStarted(this);
        }

        int i = 0;

        for (Taclet taclet : taclets) {
            InitConfig initConfig = initConfigs[i];
            initConfig.setTaclets(initConfig.getTaclets().prependReverse(axioms));
            UserDefinedSymbols symbolsForAxioms = analyzeTaclets(axioms, initConfig.namespaces());

            symbolsForAxioms.addSymbolsToNamespaces(initConfig.namespaces());

            for (LoaderListener listener : listeners) {
                listener.reportStatus(this, "Create Lemma for " + taclet.name());

            }
            singleProofs[i] = create(taclet, initConfig, symbolsForAxioms);
            i++;
        }

        ProofAggregate proofAggregate = singleProofs.length == 1 ? singleProofs[0]
                : ProofAggregate.createProofAggregate(singleProofs, createName(singleProofs));
        // listener.progressStopped(this);
        for (LoaderListener listener : listeners) {
            listener.resetStatus(this);
        }
        return proofAggregate;
    }



    private UserDefinedSymbols analyzeTaclets(ImmutableSet<Taclet> taclets,
            NamespaceSet referenceNamespaces) {
        final UserDefinedSymbols userDefinedSymbols =
            new UserDefinedSymbols(referenceNamespaces, taclets);
        TacletVisitor visitor = new TacletVisitor() {

            @Override
            public void visit(Term visited) {
                collectUserDefinedSymbols(visited, userDefinedSymbols);

            }
        };
        for (Taclet taclet : taclets) {
            visitor.visit(taclet);
        }
        return userDefinedSymbols;
    }



    private void collectUserDefinedSymbols(Term term, UserDefinedSymbols userDefinedSymbols) {
        for (Term sub : term.subs()) {
            collectUserDefinedSymbols(sub, userDefinedSymbols);
        }
        if (term.op() instanceof SortedOperator) {
            Sort sort = ((SortedOperator) term.op()).sort();
            userDefinedSymbols.addSort(sort);

            if (term.op() instanceof Function) {
                if (sort == Sort.FORMULA) {
                    userDefinedSymbols.addPredicate((Function) term.op());
                } else {
                    userDefinedSymbols.addFunction((Function) term.op());
                }
            }
            if (term.op() instanceof LogicVariable) {
                userDefinedSymbols.addVariable((LogicVariable) term.op());
            }
            if (term.op() instanceof SchemaVariable) {
                userDefinedSymbols.addSchemaVariable((SchemaVariable) term.op());
            }

        }
    }



    private ProofAggregate create(Taclet taclet, InitConfig initConfig,
            UserDefinedSymbols symbolsForAxioms) {
        LemmaGenerator generator = new GenericRemovingLemmaGenerator();
        TacletFormula tacletFormula = generator.translate(taclet, initConfig.getServices());
        Term formula = tacletFormula.getFormula(initConfig.getServices());
        String name = "Taclet: " + taclet.name().toString();

        UserDefinedSymbols userDefinedSymbols = new UserDefinedSymbols(symbolsForAxioms);

        collectUserDefinedSymbols(formula, userDefinedSymbols);
        userDefinedSymbols.replaceGenericByProxySorts();

        // In the new saving scheme, no header needs to stored
        // this is encoded in the properties of the TacletProofObligationInput.
        // (MU 2013-08)
        // String header = userDefinedSymbols.createHeader(initConfig.getServices());

        Proof proof = new Proof(name, formula, "" /* header */, initConfig);


        userDefinedSymbols.addSymbolsToNamespaces(proof.getNamespaces());

        return ProofAggregate.createProofAggregate(proof, name);
    }


}
