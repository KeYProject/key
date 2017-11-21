package de.uka.ilkd.key.macros.scripts;

import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;
import java.util.Map;
import java.util.Stack;

public class ScriptTreeParser {

    public static ScriptNode parse(Reader reader) throws IOException, ScriptException {
        
        ScriptNode root = null;
        ScriptNode last = null;
        Stack<ScriptNode> branchStack = new Stack<>();
        
        ScriptLineParser lineParser = new ScriptLineParser(reader);

        while(true) {

            int from = lineParser.getPosition();
            Map<String, String> command = lineParser.parseCommand();
            int to = lineParser.getPosition();

            if(command == null) {
                return root;
            }

            switch(command.get(ScriptLineParser.COMMAND_KEY)) {
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
                if(root == null) {
                    root = node;
                } else if(last == null) {
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
                ScriptTreeParser.parse(new InputStreamReader(System.in));
        
        root.dump(0);
        
    }
    
}
