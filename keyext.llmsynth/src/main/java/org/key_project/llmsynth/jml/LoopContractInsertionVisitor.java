package org.key_project.llmsynth.jml;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.jml.NodeWithContracts;
import com.github.javaparser.ast.jml.clauses.JmlContract;

public class LoopContractInsertionVisitor extends AbstractLoopVisitor {
    private final NodeList<Node> contracts;
    private final String methodName;

    public LoopContractInsertionVisitor(String methodName , NodeList<Node> contracts) {
        this.contracts = contracts;
        this.methodName = methodName;
    }

    @Override
    protected <T extends Node & NodeWithContracts<T>> T visitLoop(T n, T result) {
        if (n.getContracts().isEmpty() && isDesiredMethod(n)) {
            result.setContracts(contracts.stream().filter((x) -> x instanceof JmlContract).map((x) -> (JmlContract) x).collect(NodeList::new, NodeList::add, NodeList::addAll));
        }
        return result;
    }

    private boolean isDesiredMethod(Node n) {
        Node parent = n;
        do {
            parent = parent.getParentNode().orElse(null);
        } while (!(parent instanceof MethodDeclaration) && parent != null);
        if (parent == null) {
            return false;
        } else {
            return ((MethodDeclaration) parent).getNameAsString().equals(methodName);
        }
    }

}
