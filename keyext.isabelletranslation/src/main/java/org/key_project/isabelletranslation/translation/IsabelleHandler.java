/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.translation;

import java.io.IOException;
import java.util.Properties;

import de.uka.ilkd.key.java.Services;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;

/**
 * This class is a slightly adjusted version of {@link de.uka.ilkd.key.smt.newsmt2.SMTHandler}. It
 * largely has the same functionality.
 *
 * @author Mattias Ulbrich
 * @author Jonas Schiffl
 * @author Nils Buchholz
 */
public interface IsabelleHandler {

    /**
     * An enumeration of the possible answers of a handler to the {@link #canHandle(Term)} method.
     */
    enum Capability {
        /**
         * This indicates that the handler cannot translate a term
         */
        UNABLE,
        /**
         * This indicates that the handler can translate a term
         */
        YES_THIS_INSTANCE,
        /**
         * This indicates that the handler can translate any term with the same operator
         */
        YES_THIS_OPERATOR
    }

    /**
     * Initialise this handler.
     * <p>
     * This method is only called once after creation and before any other method is called.
     * <p>
     * This method may also allocate additional resources that it needs for translation.
     *
     * @param masterHandler the MasterHandler coordinating the other handlers (including the one at
     *        hand)
     * @param services the non-null services object which is relevant for this handler
     * @param handlerSnippets the snippets loaded for this handler, null if no snippet property file
     *        is available for this handler
     * @param handlerOptions arbitrary options for the handler to take into account
     * @throws IOException if resources cannot be read.
     */
    void init(IsabelleMasterHandler masterHandler, Services services, Properties handlerSnippets,
            String[] handlerOptions) throws IOException;

    /**
     * Query if this handler can translate a term.
     * <p>
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
     * <p>
     * Test if this handler can translate any term with the given argument top level operator.
     *
     * @param op a non-null operator to translate
     * @return true if this handler can successfully translate all terms with op as toplevel
     *         operator
     */
    boolean canHandle(Operator op);

    /**
     * Translate the given term into a StringBuilder.
     * <p>
     * This method will only be called if {@link #canHandle(Term)} returned true for the same term
     * argument.
     * <p>
     * The translation may add to the set of assumptions and declarations using corresponding calls
     * to the {@link IsabelleMasterHandler} that it receives.
     *
     * @param trans the non-null master handler to which it belongs
     * @param term the non-null term to translate
     * @return a StringBuilder containing the translation
     */
    StringBuilder handle(IsabelleMasterHandler trans, Term term);
}
