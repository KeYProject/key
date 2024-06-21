package org.key_project.llmsynth.jml;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.ast.body.MethodDeclaration;

public class MethodContractInsertionVisitor extends CloneVisitor {
    private final NodeList<Node> contracts;
    private final String methodName;

    public MethodContractInsertionVisitor(String methodName , NodeList<Node> contracts) {
        this.contracts = contracts;
        this.methodName = methodName;
    }

    @Override
    public Visitable visit(com.github.javaparser.ast.body.MethodDeclaration n, Object arg) {
        var result = (MethodDeclaration) super.visit(n, arg);
        if (n.getNameAsString().equals(methodName)) {
            var jmlContracts = contracts.stream().filter((x) -> x instanceof JmlContract).map((x) -> (JmlContract) x).collect(NodeList<JmlContract>::new, NodeList<JmlContract>::add, NodeList<JmlContract>::addAll);
            result.setContracts(jmlContracts);
            var modifiers = contracts.stream().filter((x) -> x instanceof Modifier).map((x) -> (Modifier) x).collect(NodeList<Modifier>::new, NodeList<Modifier>::add, NodeList<Modifier>::addAll);
            modifiers.addAll(result.getModifiers());
            result.setModifiers(modifiers);
        }
        return result;
    }
}
