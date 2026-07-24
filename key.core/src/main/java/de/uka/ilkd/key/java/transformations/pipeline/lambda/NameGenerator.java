package de.uka.ilkd.key.java.transformations.pipeline.lambda;

import com.github.javaparser.Position;
import com.github.javaparser.ast.expr.SimpleName;
import com.sun.source.tree.LineMap;

import java.util.ArrayList;
import java.util.List;

/**
 * Generates names guaranteeing uniqueness in generated names by one instance of NameGenerator.
 */
public class NameGenerator {
    private final LineMap lineMap;
    private final List<String> generatedNames;

    public NameGenerator(LineMap lineMap) {
        this.lineMap = lineMap;
        this.generatedNames = new ArrayList<>();
    }

    /**
     * Generates a unique name based on the prefix and position.
     *
     * @param prefix the prefix for the generated name
     * @param pos    the position in the source file
     * @return a unique Name
     */
    public SimpleName generate(String prefix, Position pos) {
        return generate(prefix, pos, null);
    }

    /**
     * Recursively generates a unique name.
     *
     * @param prefix  the prefix for the generated name
     * @param pos     the position in the source file
     * @param counter an optional counter for disambiguation
     * @return a unique Name
     */
    private SimpleName generate(String prefix, Position pos, Integer counter) {
        int line = pos.line;
        String newName = "%sL%d".formatted(prefix, line);
        if (counter != null) {
            newName += "_" + counter;
        }
        if (generatedNames.contains(newName)) {
            return generate(prefix, pos, counter == null ? 0 : counter + 1);
        }
        generatedNames.add(newName);
        return new SimpleName(newName);
    }
}