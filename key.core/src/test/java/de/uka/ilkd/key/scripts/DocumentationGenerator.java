package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.util.KeYResourceManager;

import java.io.FileNotFoundException;
import java.util.*;

public class DocumentationGenerator {

    private static String branch;
    private static String sha1;

    public static void main(String[] args) throws FileNotFoundException {

        if(args.length > 0) {
            System.err.println("Redirecting output to " + args[0]);
            System.setOut(new java.io.PrintStream(args[0]));
        }

        printHeader();

        Set<Map.Entry<String, ProofScriptCommand>> commands = ProofScriptEngine.loadCommands().entrySet();
        Map<String, List<Map.Entry<String, ProofScriptCommand>>> commandsByCategory = new TreeMap<>();

        for (Map.Entry<String, ProofScriptCommand> entry : commands) {
            String category = entry.getValue().getCategory();
            if (category == null) {
                category = "Uncategorized";
            }
            commandsByCategory.computeIfAbsent(category, k -> new ArrayList<>()).add(entry);
        }

        List<String> categories = new ArrayList<>(commandsByCategory.keySet());
        categories.remove("Uncategorized");
        Collections.sort(categories);

        for (String category : categories) {
            listCategory(category, commandsByCategory.get(category));
        }

        listCategory("Uncategorized", commandsByCategory.get("Uncategorized"));

    }

    private static void printHeader() {
        branch = KeYResourceManager.getManager().getBranch();
        String version = KeYResourceManager.getManager().getVersion();
        sha1 = KeYResourceManager.getManager().getSHA1();

        // This gets too technical. But this is for the key-docs repository. ...
        System.out.printf("""                
                <style>
                  nav.md-nav--secondary li.md-nav__item li.md-nav__item li.md-nav__item { display: none; }
                </style>
                # Proof Script Commands
                
                This document lists all proof script commands available in the KeY system.
                The general ideas of scripts, their syntax, and control flow are described
                in the general documentation files on proof scripts.
                
                Field | Value
                ----- | -----
                Generated on: | %s
                Branch: | %s
                Version: | %s
                Commit: | %s
                
                The commands are organised into categories. Each command may have multiple aliases
                under which it can be invoked. The first alias listed is the primary name of the command.
                There *named* and *positional* arguments. Named arguments need to be prefixed by their name
                and a colon. Positional arguments are given in the order defined by the command.
                Optional arguments are enclosed in square brackets.
                """, new Date(), branch, version, sha1);
    }

    private static void listCategory(String category, List<Map.Entry<String, ProofScriptCommand>> proofScriptCommands) {
        proofScriptCommands.sort(Map.Entry.comparingByKey());
        System.out.println("\n## Category *" + category + "*\n");
        for (Map.Entry<String, ProofScriptCommand> entry : proofScriptCommands) {
            System.out.println("<hr>\n");
            if(entry.getKey().equals(entry.getValue().getName())) {
                ProofScriptCommand command = entry.getValue();
                String link = "main".equals(branch) ? "main" : sha1;
                System.out.println("### <span style=\"color: var(--md-primary-fg-color);\"> Command `" + command.getName() + "`</span>\n\n");
                System.out.printf("<span style=\"float:right;\">[Source](https://github.com/KeYProject/key/blob/%s/key.core/src/main/java/%s.java)</span>\n\n",
                        link,
                        command.getClass().getName().replace('.', '/') );
                System.out.println(command.getDocumentation() + "\n");
                if (command.getAliases().size() > 1) {
                    System.out.println("#### Aliases:\n" + String.join(", ", command.getAliases()) + "\n");
                }
            } else {
                System.out.println("### <span style=\"color: var(--md-primary-fg-color);\"> Command `" + entry.getKey() + "`</span>\n");
                System.out.println("Alias for command [\u2192 `" + entry.getValue().getName() + "`](#command-" + entry.getValue().getName() + ")\n");
            }
        }
    }
}
