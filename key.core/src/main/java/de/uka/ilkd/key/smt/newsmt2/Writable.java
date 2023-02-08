package de.uka.ilkd.key.smt.newsmt2;

/**
 * Writeable objects have the possibility to be written to a {@link StringBuilder}.
 *
 * This avoids to explicitly invoke {@link #toString()} on larger objects which might be
 * inefficient.
 *
 * Most prominent subclass is {@link SExpr}.
 *
 * @author Mattias Ulbrich
 *
 * @see SExpr
 * @see VerbatimSMT
 */
public interface Writable {
    void appendTo(StringBuilder sb);
}
