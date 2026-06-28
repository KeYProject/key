package de.uka.ilkd.key.peg;

import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.parser.KeY;
import de.uka.ilkd.key.parser.KeYTokenManager;
import de.uka.ilkd.key.parser.ParseException;
import de.uka.ilkd.key.parser.SimpleCharStream;
import org.antlr.v4.runtime.CharStreams;

import java.io.IOException;
import java.io.StringReader;
import java.nio.file.Files;
import java.nio.file.Path;

/**
 *
 * @author Alexander Weigl
 * @version 1 (25.06.26)
 */
public class Test {
    public static void main(String[] args) throws IOException, ParseException {
        var in = Files.readString(Path.of("super.key"));
        var tm = new KeYTokenManager(new SimpleCharStream(new StringReader(in)));

        int q = 1000;
        for (int n = 1; n < q; n++) {
            double x = System.nanoTime();
            for (int i = 0; i < n; i++) {
                var k = new KeY(new StringReader(in));
                k.file();
            }
            double y = System.nanoTime();

            double a = System.nanoTime();
            for (int i = 0; i < n; i++) {
                ParsingFacade.createParser(ParsingFacade.createLexer(CharStreams.fromString(in)))
                        .file();
            }
            double b = System.nanoTime();


            System.out.printf("%2.2f\n", (y - x) / (b - a));
        }

    }
}
