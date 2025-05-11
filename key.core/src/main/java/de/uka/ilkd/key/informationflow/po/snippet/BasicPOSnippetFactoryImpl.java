/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import java.lang.reflect.InvocationTargetException;
import java.util.EnumMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.speclang.LoopSpecification;

import org.jspecify.annotations.NonNull;
import org.key_project.logic.TermCreationException;

import org.slf4j.LoggerFactory;

/**
 *
 * @author christoph
 */
class BasicPOSnippetFactoryImpl implements BasicPOSnippetFactory {
    private static final org.slf4j.Logger LOGGER =
        LoggerFactory.getLogger(BasicPOSnippetFactoryImpl.class);

    /**
     * Collection of data important for the production of snippets.
     */
    private final BasicSnippetData data;

    /**
     * Variables belonging to the proof obligation.
     */
    private final ProofObligationVars poVars;

    /**
     * Registered snippet factory methods.
     */
    private final EnumMap<Snippet, FactoryMethod> factoryMethods =
        new EnumMap<>(Snippet.class);


    BasicPOSnippetFactoryImpl(BasicSnippetData data, ProofObligationVars poVars) {
        this.data = data;
        this.poVars = poVars;
        registerFactoryMethods();
    }


    BasicPOSnippetFactoryImpl(@NonNull FunctionalOperationContract contract, ProofObligationVars poVars,
                              @NonNull Services services) {
        this.data = new BasicSnippetData(contract, services);
        this.poVars = poVars;
        registerFactoryMethods();
    }

    BasicPOSnippetFactoryImpl(@NonNull LoopSpecification invariant, ProofObligationVars poVars,
                              ExecutionContext context, @NonNull Term guardTerm, @NonNull Services services) {
        this.data = new BasicSnippetData(invariant, context, guardTerm, services);
        this.poVars = poVars;
        registerFactoryMethods();
    }


    BasicPOSnippetFactoryImpl(@NonNull InformationFlowContract contract, ProofObligationVars poVars,
                              @NonNull Services services) {
        this.data = new BasicSnippetData(contract, services);
        this.poVars = poVars;
        registerFactoryMethods();
    }


    BasicPOSnippetFactoryImpl(@NonNull BlockContract contract, ProofObligationVars poVars,
                              ExecutionContext context, @NonNull Services services) {
        this.data = new BasicSnippetData(contract, context, services);
        this.poVars = poVars;
        registerFactoryMethods();
    }


    private void registerFactoryMethods() {
        try {
            for (Snippet s : Snippet.values()) {
                FactoryMethod fm = (FactoryMethod) s.c.getDeclaredConstructor().newInstance();
                factoryMethods.put(s, fm);
            }
        } catch (InstantiationException | SecurityException | NoSuchMethodException
                | InvocationTargetException | IllegalArgumentException
                | IllegalAccessException ex) {
            LOGGER.error("Failed to register factory methods", ex);
        }
    }


    @Override
    public Term create(@NonNull Snippet snippet) throws UnsupportedOperationException {
        try {
            FactoryMethod m = factoryMethods.get(snippet);
            if (m == null) {
                throw new UnsupportedOperationException(
                    "Unknown factory " + "method for snippet \"" + snippet.name() + ".");
            }
            return m.produce(data, poVars);
        } catch (TermCreationException e) {
            throw new UnsupportedOperationException("Factory method for " + "snippet \""
                + snippet.name() + " threw " + "TermCreationException: " + e.getMessage(), e);
        }
    }

}
