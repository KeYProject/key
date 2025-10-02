package de.uka.ilkd.key.scripts;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.dataformat.yaml.YAMLFactory;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.util.KeYResourceManager;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class DocumentationGenerator {

    public static void main(String[] args) throws FileNotFoundException {

        if(args.length > 0) {
            System.err.println("Redirecting output to " + args[0]);
            System.setOut(new java.io.PrintStream(args[0]));
        }

        printHeader();

        Collection<ProofScriptCommand> commands = ProofScriptEngine.loadCommands().values();
        Map<String, List<ProofScriptCommand>> commandsByCategory = new TreeMap<>();

        for (ProofScriptCommand command : commands) {
            String category = command.getCategory();
            if (category == null) {
                category = "Uncategorized";
            }
            commandsByCategory.computeIfAbsent(category, k -> new ArrayList<>()).add(command);
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
        String branch = KeYResourceManager.getManager().getBranch();
        String version = KeYResourceManager.getManager().getVersion();
        String sha1 = KeYResourceManager.getManager().getSHA1();

        System.out.printf("""
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

    private static void listCategory(String category, List<ProofScriptCommand> proofScriptCommands) {
        Set<ProofScriptCommand> alreadyListed = new HashSet<>();
        System.out.println("\n## Category *" + category + "*\n");
        for (ProofScriptCommand command : proofScriptCommands) {
            if(alreadyListed.contains(command))
                continue;
            alreadyListed.add(command);
            System.out.println("<hr>\n");
            System.out.println("### <span style=\"color: var(--md-primary-fg-color);\"> Command `" + command.getName() + "`</span>\n");
            System.out.println(command.getDocumentation() + "\n");
            if(command.getAliases().size() > 1) {
                System.out.println("#### Aliases:\n" + String.join(", ", command.getAliases()) + "\n");
            }
        }
    }
}
