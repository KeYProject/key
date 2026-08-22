package de.uka.ilkd.key.java.transformations.pipeline.lambda.analyzer;

import java.util.*;

/**
 * Locates and extracts free variables from Java trees.
 */
public class FreeVariablesLocator extends JmlTreeScanner {

    /**
     * Tracks the binding status of variables during traversal.
     */
    private static class VariableBindingStatus {
        private final Set<Symbol> innerFreeVariables = new HashSet<>();
        private final Set<Symbol> boundVariables = new HashSet<>();

        /**
         * Adds all symbols as bound variables.
         *
         * @param syms the symbols to add as bound
         */
        void addAllBound(Collection<Symbol> syms) {
            for (Symbol sym : syms) {
                boundVariables.add(sym);
            }
            // Ensure uniqueness by name
            Set<NameWrapper> seen = new HashSet<>();
            boundVariables.removeIf(sym -> !seen.add(new NameWrapper(sym.name.toString())));
        }

        /**
         * Adds all symbols as free variables.
         *
         * @param syms the symbols to add as free
         */
        void addAllFree(Collection<Symbol> syms) {
            for (Symbol sym : syms) {
                innerFreeVariables.add(sym);
            }
            // Ensure uniqueness by name
            Set<NameWrapper> seen = new HashSet<>();
            innerFreeVariables.removeIf(sym -> !seen.add(new NameWrapper(sym.name.toString())));
        }

        /**
         * Gets the set of free variables (free minus bound).
         *
         * @return the set of free variables
         */
        Set<Symbol> getFreeVariables() {
            Set<Symbol> result = new HashSet<>(innerFreeVariables);
            result.removeAll(boundVariables);
            // Ensure uniqueness by name
            Set<NameWrapper> seen = new HashSet<>();
            result.removeIf(sym -> !seen.add(new NameWrapper(sym.name.toString())));
            return result;
        }

        /**
         * Adds a single symbol as a free variable.
         *
         * @param sym the symbol to add
         */
        void addFree(Symbol sym) {
            addAllFree(Collections.singletonList(sym));
        }

        /**
         * Adds a single symbol as a bound variable.
         *
         * @param sym the symbol to add
         */
        void addBound(Symbol sym) {
            addAllBound(Collections.singletonList(sym));
        }
    }

    /**
     * Wrapper class for comparing names by string value.
     */
    private static class NameWrapper {
        private final String name;

        NameWrapper(String name) {
            this.name = name;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            NameWrapper that = (NameWrapper) o;
            return Objects.equals(name, that.name);
        }

        @Override
        public int hashCode() {
            return Objects.hash(name);
        }
    }

    private final VariableBindingStatus variablesBindings;
    private final JmlTree.Maker maker;
    private final Names names;

    /**
     * Constructs a FreeVariablesLocator.
     *
     * @param context the javac context
     */
    public FreeVariablesLocator(Context context) {
        this.context = context;
        this.variablesBindings = new VariableBindingStatus();
        this.maker = JmlTree.Maker.instance(context);
        this.names = Names.instance(context);
    }

    /**
     * Convenience method for extracting free variables from multiple trees.
     *
     * @param trees the trees to analyze
     * @return the set of free variable symbols
     */
    public Set<Symbol> extractFreeVariables(JCTree... trees) {
        for (JCTree tree : trees) {
            if (tree != null) {
                tree.accept(this);
            }
        }
        return variablesBindings.getFreeVariables();
    }

    @Override
    public void visitJmlQuantifiedExpr(JmlTree.JmlQuantifiedExpr that) {
        FreeVariablesLocator nested = new FreeVariablesLocator(context);
        Set<Symbol> vars = nested.extractFreeVariables(that.racexpr, that.racexpr, that.value);

        Set<Symbol> declSymbols = new HashSet<>();
        for (JmlTree.JmlVariableDecl decl : that.decls) {
            declSymbols.add(decl.sym);
        }

        Set<Symbol> freeVars = new HashSet<>(vars);
        freeVars.removeAll(declSymbols);
        variablesBindings.addAllFree(freeVars);
    }

    @Override
    public void visitMethodDef(JCTree.JCMethodDecl tree) {
        FreeVariablesLocator nested = new FreeVariablesLocator(context);
        Set<Symbol> vars = nested.extractFreeVariables(tree.body);

        Set<Symbol> paramSymbols = new HashSet<>();
        for (JCTree.JCVariableDecl param : tree.params) {
            paramSymbols.add(param.sym);
        }

        Set<Symbol> freeVars = new HashSet<>(vars);
        // Filter out 'this' references
        freeVars.removeIf(sym -> sym.name.equals(names._this));
        freeVars.removeAll(paramSymbols);
        variablesBindings.addAllFree(freeVars);
    }

    @Override
    public void visitVarDef(JCTree.JCVariableDecl tree) {
        variablesBindings.addBound(tree.sym);
        super.visitVarDef(tree);
    }

    @Override
    public void visitAnnotation(JCTree.JCAnnotation tree) {
        System.out.println("ignore annotation " + tree);
        // Don't traverse into annotations
    }

    @Override
    public void visitLambda(JCTree.JCLambda tree) {
        FreeVariablesLocator nested = new FreeVariablesLocator(context);
        Set<Symbol> vars = nested.extractFreeVariables(tree.body);

        Set<Symbol> paramSymbols = new HashSet<>();
        for (JCTree.JCVariableDecl param : tree.params) {
            paramSymbols.add(param.sym);
        }

        Set<Symbol> freeVars = new HashSet<>(vars);
        freeVars.removeAll(paramSymbols);
        variablesBindings.addAllFree(freeVars);
    }

    @Override
    public void visitIdent(JCTree.JCIdent tree) {
        if (tree.name.toString().isEmpty()) {
            return;
        }
        if (tree.sym == null) {
            // FIXME this case can be removed if types are regenerated after each lambda-replacement pass
            return;
        }
        if (tree.sym instanceof Symbol.ClassSymbol) {
            // Class-Symbols are no free variables
            return;
        }
        if (tree.sym.owner instanceof Symbol.ClassSymbol && !tree.name.toString().equals("this")) {
            JCTree.JCIdent ref = (JCTree.JCIdent) maker.This(tree.sym.owner.type);
            variablesBindings.addFree(ref.sym);
            return;
        }
        variablesBindings.addFree(tree.sym);
    }
}