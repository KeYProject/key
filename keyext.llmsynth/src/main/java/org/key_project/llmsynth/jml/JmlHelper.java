package org.key_project.llmsynth.jml;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.Problem;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.jml.doc.JmlDocStmt;
import com.github.javaparser.jml.JmlDocSanitizer;

import java.util.HashSet;
import java.util.stream.Collectors;

public class JmlHelper {

    public static NodeList<Node> parseFragment(String fragment) throws ParsingException {
        // Load file
        ParserConfiguration configuration = new ParserConfiguration();
        configuration.setProcessJml(false);
        JavaParser p = new JavaParser(configuration);
        var result = p.parseStatement(fragment);
        if (result.isSuccessful()) {
            JmlDocStmt jmlDocStmt = (JmlDocStmt) result.getResult().get();
            var sanitizer = new JmlDocSanitizer(new HashSet<>());
            var jmlContent = sanitizer.asString(jmlDocStmt.getJmlComments());
            var contracts = p.parseJmlMethodLevel(jmlContent);
            if (contracts.isSuccessful()) {
                return contracts.getResult().get().getChildren();
            } else {
                throw new ParsingException("Failed to parse JML fragment: " + contracts.getProblems().stream().map(Problem::getMessage).collect(Collectors.joining(", ")));
            }
            //return contract.getResult().get().getChildren().stream().map((x) -> (JmlContract) x).collect(NodeList::new, NodeList::add, NodeList::addAll);
        } else {
            throw new ParsingException("Failed to parse JML fragment: " + result.getProblems().stream().map(Problem::getMessage).collect(Collectors.joining(", ")));
        }
    }

    public static CompilationUnit parseFile(String join) throws ParsingException {
        ParserConfiguration configuration = new ParserConfiguration();
        configuration.setProcessJml(true);
        JavaParser p = new JavaParser(configuration);
        var result = p.parse(join);
        if (result.isSuccessful()) {
            return result.getResult().get();
        } else {
            throw new ParsingException("Failed to parse file: " + result.getProblems().stream().map(Problem::getMessage).toString());
        }
    }

    public static CompilationUnit addMethodContract(CompilationUnit cu, String methodName, NodeList<Node> contracts) {
        var visitor = new MethodContractInsertionVisitor(methodName, contracts);
        return (CompilationUnit) visitor.visit(cu, null);
    }

    public static CompilationUnit addLoopInvariant(CompilationUnit cu, String methodName, NodeList<Node> contracts) {
        var visitor = new LoopContractInsertionVisitor(methodName, contracts);
        return (CompilationUnit) visitor.visit(cu, null);
    }
}
