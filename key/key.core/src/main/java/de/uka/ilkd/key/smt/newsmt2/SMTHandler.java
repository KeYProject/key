package de.uka.ilkd.key.smt.newsmt2;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.smt.SMTTranslationException;

import java.io.IOException;
import java.util.Properties;

/**
 * General interface for routines that translate particular KeY data structures
 * to SMT.
 *
 * SMT handlers are loaded via a {@link java.util.ServiceLoader}.
 *
 * To implement a new handler, implement this interface and add the classname to
 * a file that ServiceLoader reads for SMTHandler.
 *
 * <h2>Procedure</h2>
 *
 * SMT handlers are created using the default constructor without parameters
 * They are always used within the same proof, but possibly for several proof
 * obligations.
 *
 * After creation, the {@link #init(MasterHandler, Services, Properties)} method is called that injects the
 * {@link Services} object belonging to the proof.
 *
 * During translation, an SMT handler can be asked via {@link #canHandle(Term)}
 * if it can translate a term into smt.
 *
 * If it returns true, the method {@link #handle(MasterHandler, Term)} will be
 * called which returns the SMT result in form of an {@link SExpr}.
 *
 * @author Mattias Ulbrich
 * @author Jonas Schiffl
 */
public interface SMTHandler {

    /**
     * Initialise this handler.
     *
     * This method is only called once after creation and before any other
     * method is called.
     *
     * This method may also allocate additional resources that it needs for
     * translation.
     *
     *
     * @param masterHandler
     * @param services the non-null services object which is relevant for
     *                 this handler
     * @param handlerSnippets the snippets loaded for this handler, null if no
     *                        snippet property file is available for this handler
     * @throws IOException if resources cannot be read.
     */
    void init(MasterHandler masterHandler, Services services, Properties handlerSnippets) throws IOException;

    /**
     * Query if this handler can translate a term.
     *
     * Test if this term can translate the given argument.
     * Usually this requires checking whether the toplevel operator of the term
     * is in the list of supported operators.
     *
     * @param term a non-null term to translate
     * @return true if this handler can successfully translate the term
     */
    boolean canHandle(Term term);

    /**
     * Translate the given term into an SMT SExpression.
     *
     * This method will only be called if {@link #canHandle(Term)} returned
     * true for the same term argument.
     *
     * The translation may add to the set of assumptions and declarations using
     * corresponding calls to the {@link MasterHandler} that it receives.
     *
     * @param trans the non-null master handler to which it belongs
     * @param term the non-null term to translate
     * @return an SExpr representing the term
     * @throws SMTTranslationException if the translation fails unexpectedly.
     */
    SExpr handle(MasterHandler trans, Term term) throws SMTTranslationException;

}
