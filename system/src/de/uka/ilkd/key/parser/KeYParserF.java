// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.parser;

import java.util.HashMap;

import org.antlr.runtime.LegacyCommonTokenStream;
import org.antlr.runtime.TokenStream;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.JavaReader;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.rule.Taclet;
import org.antlr.runtime.RecognitionException;

/**
 * Extends generated class {@link KeYParser} with custom constructors.
 */
public class KeYParserF extends KeYParser {

    private static boolean isSelectTerm(Term term) {
        return term.op().name().toString().endsWith("::select") && term.arity() == 3;
    }

    private boolean isImplicitHeap(Term t) {
        return getServices().getTermBuilder().getBaseHeap().equals(t);
    }

    // This is also used in TestTermParserHeap.java
    public static final String NO_HEAP_EXPRESSION_BEFORE_AT_EXCEPTION_MESSAGE =
            "Expecting select term before '@', not: ";

    private Term replaceHeap(Term term, Term heap, int depth) throws RecognitionException {
        if (depth > 0) {

            if (isSelectTerm(term)) {

                if (!isImplicitHeap(term.sub(0))) {
                    semanticError("Expecting program variable heap as first argument of: " + term);
                }

                Term[] params = new Term[]{heap, replaceHeap(term.sub(1), heap, depth - 1), term.sub(2)};
                return (getServices().getTermFactory().createTerm(term.op(), params));

            } else if (term.op() instanceof ObserverFunction) {
                if (!isImplicitHeap(term.sub(0))) {
                    semanticError("Expecting program variable heap as first argument of: " + term);
                }

                Term[] params = new Term[term.arity()];
                params[0] = heap;
                params[1] = replaceHeap(term.sub(1), heap, depth - 1);
                for(int i = 2; i < params.length; i++) {
                    params[i] = term.sub(i);
                }

                return (getServices().getTermFactory().createTerm(term.op(), params));

            } else {
                semanticError(NO_HEAP_EXPRESSION_BEFORE_AT_EXCEPTION_MESSAGE + term);
                throw new RecognitionException();
            }

        } else {
            return term;
        }
    }

    @Override
    protected Term heapSelectionSuffix(Term term, Term heap) throws RecognitionException {

        if (!isHeapTerm(heap)) {
            semanticError("Expecting term of type Heap but sort is " + heap.sort()
                    + " for term: " + term);
        }

        Term result = replaceHeap(term, heap, globalImplicitHeapSuffixCounter);

        // reset globalImplicitHeapSuffixCounter
        globalImplicitHeapSuffixCounter = 0;

        return result;
    }

    public KeYParserF(ParserMode mode, KeYLexerF keYLexerF,
            ParserConfig schemaConfig, ParserConfig normalConfig,
            HashMap taclet2Builder, ImmutableSet<Taclet> taclets) {
        super(mode, new LegacyCommonTokenStream(keYLexerF), schemaConfig,
                normalConfig, taclet2Builder, taclets);
    }

    public KeYParserF(ParserMode mode, TokenStream lexer,
            ParserConfig schemaConfig, ParserConfig normalConfig,
            HashMap taclet2Builder, ImmutableSet<Taclet> taclets) {
        super(mode, lexer, schemaConfig, normalConfig, taclet2Builder, taclets);
    }

    public KeYParserF(ParserMode mode, KeYLexerF keYLexerF) {
        super(mode, new LegacyCommonTokenStream(keYLexerF));
    }

    public KeYParserF(ParserMode mode, KeYLexerF keYLexerF,
            JavaReader jr, Services services, NamespaceSet nss, AbbrevMap scm) {
        super(mode, new LegacyCommonTokenStream(keYLexerF), jr, services, nss, scm);
    }

    public KeYParserF(ParserMode mode, KeYLexerF keYLexerF, Services services, NamespaceSet nss) {
        super(mode, new LegacyCommonTokenStream(keYLexerF), services, nss);
    }

}
