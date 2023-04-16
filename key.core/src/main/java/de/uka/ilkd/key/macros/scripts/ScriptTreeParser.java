package de.uka.ilkd.key.macros.scripts;

import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.Map;

public class ScriptTreeParser {

    public static ScriptNode parse(Reader reader) throws IOException, ScriptException {

        ScriptNode root = null;
        ScriptNode last = null;
        ArrayDeque<ScriptNode> branchStack = new ArrayDeque<>();

        ScriptLineParser lineParser = new ScriptLineParser(reader, null);

        while (true) {

            int from = lineParser.getOffset();
            Map<String, String> command = lineParser.parseCommand();
            int to = lineParser.getOffset();

            if (command == null) {
                return root;
            }

            switch (command.get(ScriptLineParser.COMMAND_KEY)) {
            case "branches":
                branchStack.push(last);
                break;
            case "next":
                last = branchStack.peek();
                break;
            case "end":
                last = null;
                branchStack.pop();
                break;
            default:
                ScriptNode node = new ScriptNode(last, command, from, to);
                if (root == null) {
                    root = node;
                } else if (last == null) {
                    throw new ScriptException("unexpected last");
                } else {
                    last.addNode(node);
                }
                last = node;
                break;
            }
        }

    }

    public static void main(String[] args) throws IOException, ScriptException {

        ScriptNode root =
            ScriptTreeParser.parse(new InputStreamReader(System.in, StandardCharsets.UTF_8));

        root.dump(0);

    }

}
