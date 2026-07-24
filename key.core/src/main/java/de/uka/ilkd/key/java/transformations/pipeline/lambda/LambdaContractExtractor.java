package de.uka.ilkd.key.java.transformations.pipeline.lambda;

import com.sun.tools.javac.util.List;

public class LambdaContractExtractor extends JmlTreeScanner {
    public List<JmlTree.JmlSpecificationCase> spec;

    @Override
    public void visitJmlBlock(JmlTree.JmlBlock that) {
        super.visitJmlBlock(that);
    }

    @Override
    public void visitJmlStatementSpec(JmlTree.JmlStatementSpec tree) {
        this.spec = tree.statementSpecs.cases;
        tree.statementSpecs.cases = List.nil();
        super.visitJmlStatementSpec(tree);
    }

    @Override
    public void visitJmlStatement(JmlTree.JmlStatement that) {
        System.out.println("ads");
        super.visitJmlStatement(that);
    }
}
