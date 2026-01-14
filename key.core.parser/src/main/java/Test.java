import org.key_project.key.parser.KeyCCParser;
import org.key_project.key.parser.ParseException;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

/**
 *
 * @author Alexander Weigl
 * @version 1 (1/14/26)
 */
public class Test {
    public static void main(String[] args) throws ParseException, IOException {
        var path = Paths.get("mega.key").toAbsolutePath();

        /*
        try (var stream = Files.newBufferedReader(path)) {
            var jj_input_stream = new SimpleCharStream(stream, 1, 1);
            var token_source = new KeyCCParserTokenManager(jj_input_stream);

            Token tok;
            do {
                tok = token_source.getNextToken();
                System.out.format("%03d (% 5d|% 2d) : %s%n", tok.kind, tok.beginLine, tok.beginColumn, tok.image);

            } while (tok.kind != KeyCCParserConstants.EOF);
        }
        System.exit(0);
         */

        var start = System.nanoTime();
        try {
            var parser = new KeyCCParser(Files.newBufferedReader(path));
            parser.file();
        } finally {
            var stop = System.nanoTime();
            final var time = (stop - start) / 1000.0 / 1000.0;
            System.out.println(time);
        }
    }
}
