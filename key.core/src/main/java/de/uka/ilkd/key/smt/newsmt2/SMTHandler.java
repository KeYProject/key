/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.io.IOException;
import java.util.Collections;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.smt.SMTTranslationException;

/**
 * General interface for routines that translate particular KeY data structures to SMT.
 *
 * SMT handlers are loaded via a {@link java.util.ServiceLoader}.
 *
 * To implement a new handler, implement this interface and add the classname to a file that
 * ServiceLoader reads for SMTHandler.
 *
 * <h2>Procedure</h2>
 *
 * SMT handlers are created using the default constructor without parameters They are always used
 * within the same proof, but possibly for several proof obligations.
 *
 * After creation, the {@link #init(MasterHandler, Services, Properties)} method is called that
 * injects the {@link Services} object belonging to the proof.
 *
 * During translation, an SMT handler can be asked via {@link #canHandle(Term)} if it can translate
 * a term into smt.
 *
 * If it returns true, the method {@link #handle(MasterHandler, Term)} will be called which returns
 * the SMT result in form of an {@link SExpr}.
 *
 * @author Mattias Ulbrich
 * @author Jonas Schiffl
 */
public interface SMTHandler {

    /**
     * An enumeration of the possible answers of an handler to the {@link #canHandle(Term)} method.
     */
    enum Capability {
        /** This indicates that the handler cannot translate a term */
        UNABLE,
        /** This indicates that the handler can translate a term */
        YES_THIS_INSTANCE,
        /** This indicates that the handler can translate any term with the same operator */
        YES_THIS_OPERATOR
    }

    /**
     * Initialise this handler.
     *
     * This method is only called once after creation and before any other method is called.
     *
     * This method may also allocate additional resources that it needs for translation.
     *
     *
     * @param masterHandler the MasterHandler coordinating the other handlers (including the one at
     *        hand)
     * @param services the non-null services object which is relevant for this handler
     * @param handlerSnippets the snippets loaded for this handler, null if no snippet property file
     *        is available for this handler
     * @param handlerOptions arbitrary options for the handler to take into account
     * @throws IOException if resources cannot be read.
     */
    void init(MasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) throws IOException;

    /**
     * Query if this handler can translate a term.
     *
     * Test if this particular term can be translated. Usually this requires checking whether the
     * toplevel operator of the term is in the list of supported operators, but the handler can also
     * choose to use other aspects of the term to decide.
     *
     * @param term a non-null term to translate
     * @return {@link Capability#YES_THIS_OPERATOR} if this handler can successfully translate any
     *         term with the same toplevel operator, {@link Capability#YES_THIS_INSTANCE} if this
     *         handler can successfully translate this particular term, {@link Capability#UNABLE} if
     *         this handler cannot deal with the term.
     */
    default Capability canHandle(Term term) {
        return canHandle(term.op()) ? Capability.YES_THIS_OPERATOR : Capability.UNABLE;
    }

    /**
     * Query if this handler can translate an operator.
     *
     * Test if this handler can translate any term with the given argument top level operator.
     *
     * @param op a non-null operator to translate
     * @return true if this handler can successfully translate all terms with op as toplevel
     *         operator
     */
    boolean canHandle(Operator op);

    /**
     * Translate the given term into an SMT SExpression.
     *
     * This method will only be called if {@link #canHandle(Term)} returned true for the same term
     * argument.
     *
     * The translation may add to the set of assumptions and declarations using corresponding calls
     * to the {@link MasterHandler} that it receives.
     *
     * @param trans the non-null master handler to which it belongs
     * @param term the non-null term to translate
     * @return an SExpr representing the term
     * @throws SMTTranslationException if the translation fails unexpectedly.
     */
    SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException;

    /**
     * Any handler can offer a collection of properties that can be set in the GUI/script to control
     * the translation.
     *
     * The returned list is used in {@link SMTHandlerServices} and will not be modified.
     *
     * @return the non-null list of properties that this handler supports and reads.
     */
    default List<SMTHandlerProperty<?>> getProperties() {
        return Collections.emptyList();
    }

}
