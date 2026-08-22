package de.uka.ilkd.key.java.transformations.pipeline.lambda.transform;

import com.sun.tools.javac.util.List;
import org.jmlspecs.openjml.JmlTokenKind;
import org.jmlspecs.openjml.JmlTree;

/**
 * Utility class for converting contracts to model methods.
 */
public class ContractToModelMethods {
    /**
     * Converts a contract to a model method declaration.
     *
     * @param maker the JML tree maker
     * @param contracts the JML method clause contract
     * @return a JML method clause declaration with MODEL token
     */
    public static JmlTree.JmlMethodClauseDecl contractToModelMethod(
            JmlTree.Maker maker, JmlTree.JmlMethodClause contracts) {
        // Both REQUIRES and other contract types are converted to MODEL
        return maker.JmlMethodClauseDecl(JmlTokenKind.MODEL, List.nil());
    }
}