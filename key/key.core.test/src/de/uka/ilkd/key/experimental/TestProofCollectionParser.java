package de.uka.ilkd.key.experimental;

import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.Map;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
import org.antlr.runtime.TokenStream;
import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.parser.test.ProofCollectionLexer;
import de.uka.ilkd.key.parser.test.ProofCollectionParser;

class TestProofCollectionParser {

    public static void main(String[] args) throws IOException, RecognitionException {
        String fileName = System.getenv("KEY_HOME") + "/key/key.core.test/src/de/uka/ilkd/key/experimental/automaticJAVADL.txt";
        File file = new File(fileName);
        CharStream charStream = new ANTLRStringStream(IOUtil.readFrom(file));
        ProofCollectionLexer lexer = new ProofCollectionLexer(charStream);
        TokenStream tokenStream = new CommonTokenStream(lexer);
//        printTokenStream(tokenStream);
        ProofCollectionParser parser = new ProofCollectionParser(tokenStream);
        ProofCollectionParser.parserEntryPoint_return parserEntryPoint = parser.parserEntryPoint();
        List<ProofCollectionUnit> units = parserEntryPoint.units;
        Map<Token, Token> settingsMap = parserEntryPoint.settingsMap;
        for (ProofCollectionUnit u : units) {
            System.out.println(u);
        }
    }

    static void printTokenStream(TokenStream tokenStream) {
        while (true) {
            Token t = tokenStream.LT(1);
            tokenStream.consume();
            System.out.println(t);
            if (t.getType() == Token.EOF) {
                System.exit(0);
            }
        }
    }

}
