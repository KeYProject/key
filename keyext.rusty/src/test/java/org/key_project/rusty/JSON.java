package org.key_project.rusty;

import org.junit.jupiter.api.Test;
import org.key_project.rusty.parser.hir.Crate;

import java.io.*;

public class JSON {
    @Test
    void testJSON() {
        var file = new File("./src/test/resources/out.json");
        try {
            var reader = new BufferedReader(new FileReader(file));
            var sb = new StringBuilder();
            String line = reader.readLine();
            while (line != null) {
                sb.append(line);
                sb.append(System.lineSeparator());
                line = reader.readLine();
            }
            var json = sb.toString();
            var crate = Crate.parseJSON(json);
            System.out.println(crate);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
