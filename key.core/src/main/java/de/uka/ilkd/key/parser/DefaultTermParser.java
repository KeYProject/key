/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

import java.io.IOException;
import java.io.Reader;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.AbbrevMap;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.RecognitionException;


/**
 * This class wraps the default KeY-Term-Parser.
 *
 * @author Hubert Schmid
 * @author weigl
 * @deprecated Use the facade new KeyIO(services).parseTerm directly
 */
@Deprecated // java11:(forRemoval = true, since = "2.8.0")
public final class DefaultTermParser {

    /**
     * The method reads the input and parses a term with the specified namespaces. The method
     * ensures, that the term has the specified sort.
     *
     * @param sort The expected sort of the term.
     * @return The parsed term of the specified sort.
     * @throws ParserException The method throws a ParserException, if the input could not be parsed
     *         correctly or the term has an invalid sort.
     */
    public Term parse(Reader in, Sort sort, Services services,
            Namespace<QuantifiableVariable> var_ns, Namespace<Function> func_ns,
            Namespace<Sort> sort_ns, Namespace<IProgramVariable> progVar_ns, AbbrevMap scm)
            throws ParserException {
        return parse(in, sort, services, new NamespaceSet(var_ns, func_ns, sort_ns,
            new Namespace<>(), new Namespace<>(), progVar_ns), scm);
    }


    /**
     * The method reads the input and parses a term with the specified namespaces. The method
     * ensures, that the term has the specified sort.
     *
     * @param sort The expected sort of the term; must not be null.
     * @return The parsed term of the specified sort.
     * @throws ParserException The method throws a ParserException, if the input could not be parsed
     *         correctly or the term has an invalid sort.
     */
    public Term parse(Reader in, Sort sort, Services services, NamespaceSet nss, AbbrevMap scm)
            throws ParserException {
        KeyIO keyIO = new KeyIO(services, nss);
        keyIO.setAbbrevMap(scm);
        try {
            Term result = keyIO.parseExpression(CharStreams.fromReader(in));
            if (sort != null && !result.sort().extendsTrans(sort)) {
                throw new ParserException(
                    "Expected sort " + sort + ", but parser returns sort " + result.sort() + ".",
                    null);
            }
            return result;
        } catch (RecognitionException re) {
            // problemParser cannot be null since exception is thrown during parsing.
            // String message = parser.getErrorMessage(re);
            throw new RuntimeException(re); // message, new Location(re)).initCause(re);
        } catch (IOException tse) {
            throw new ParserException(tse.getMessage(), null).initCause(tse);
        }
    }

    /**
     * The method reads the input and parses a sequent with the specified namespaces.
     *
     * @return the paresed String as Sequent Object
     * @throws ParserException The method throws a ParserException, if the input could not be parsed
     *         correctly
     */
    public Sequent parseSeq(Reader in, Services services, NamespaceSet nss, AbbrevMap scm)
            throws ParserException {
        KeyIO keyIO = new KeyIO(services, nss);
        keyIO.setAbbrevMap(scm);
        try {
            final Sequent seq = keyIO.parseSequent(CharStreams.fromReader(in));
            // p = new KeYParserF(ParserMode.TERM, new KeYLexerF(in, ""), new Recoder2KeY(services,
            // nss), services, nss, scm);
            return seq;
        } catch (RecognitionException re) {
            // problemParser cannot be null since exception is thrown during parsing.
            // String message = p.getErrorMessage(re);
            // throw new ParserException(message, new Location(re));
            throw new RuntimeException(re);
        } catch (IOException tse) {
            throw new ParserException(tse.getMessage(), null);
        }
    }


}
