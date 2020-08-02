package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.smt.SMTProofParser.ProofContext;
import de.uka.ilkd.key.smt.SMTProofParser.S_exprContext;
import de.uka.ilkd.key.smt.SMTProofParser.SmtoutputContext;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.RecognitionException;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.Reader;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

public class SMTProofParsing {


    public static SmtoutputContext parse(String s) {
        return parse(CharStreams.fromString(s));
    }

    public static SmtoutputContext parse(Path path) throws IOException {
        return parse(CharStreams.fromPath(path.toAbsolutePath()));
    }

    public static SmtoutputContext parse(InputStream inputStream) throws IOException {
        return parse(CharStreams.fromStream(inputStream));
    }

    public static SmtoutputContext parse(Reader r) throws IOException {
        return parse(CharStreams.fromReader(r));
    }

    private static SmtoutputContext parse(CharStream input) {
        SMTProofLexer lexer = new SMTProofLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        //UnbufferedTokenStream<CommonToken> tokens = new UnbufferedTokenStream<>(lexer);
        SMTProofParser parser = new SMTProofParser(tokens);
        BailOutErrorStrategy errorStrategy = new BailOutErrorStrategy();
        parser.setErrorHandler(errorStrategy);
        SmtoutputContext result = null;
        try {
            SmtoutputContext tree = parser.smtoutput();
            //Visitor visitor = new Visitor();
            //for (SMTProofParser.S_exprContext ctx : tree.s_expr()) {
            //    result.add(ctx.accept(visitor));
            //}
            return tree;
        } catch (RecognitionException ex) {
            errorStrategy.reportError(parser, ex);
            throw ex;
        } catch (RuntimeException rex) {
            if (rex.getCause() instanceof RecognitionException) {
                errorStrategy.reportError(parser,
                        (RecognitionException) rex.getCause()
                );
                throw rex;
            }
        }
        return result;
    }
}