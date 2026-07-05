package de.uka.ilkd.key.java.transformations.pipeline.lambda.transform;

import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;
import org.jmlspecs.openjml.JmlTree;

/**
 * Renames variables in a JML tree by replacing occurrences of a specified name with a new name.
 */
public class RenameVariable extends JmlTreeTranslator {

    private final Name currentName;
    private final Context context;
    private final java.util.function.Function<Name, Name> replacer;
    private final JmlTree.Maker maker;

    /**
     * Constructs a RenameVariable visitor.
     *
     * @param currentName the name to replace
     * @param context the javac context
     * @param replacer a function that takes the current name and returns the replacement name
     */
    public RenameVariable(Name currentName, Context context, java.util.function.Function<Name, Name> replacer) {
        this.currentName = currentName;
        this.context = context;
        this.replacer = replacer;
        this.maker = JmlTree.Maker.instance(context);
    }

    @Override
    public <T extends JCTree> T translate(T tree) {
        if (tree == null) {
            return null;
        }

        if (tree instanceof JCTree.JCIdent) {
            JCTree.JCIdent ident = (JCTree.JCIdent) tree;
            if (ident.name.equals(currentName)) {
                Name newName = replacer.apply(ident.name);
                Symbol.VarSymbol newSym = new Symbol.VarSymbol(
                    ident.sym.flags(),
                    newName,
                    ident.type,
                    ident.sym.owner
                );
                return (T) maker.Ident(newSym);
            }
        } else if (tree instanceof JCTree.JCVariableDecl) {
            JCTree.JCVariableDecl varDecl = (JCTree.JCVariableDecl) tree;
            if (varDecl.name.equals(currentName)) {
                Name newName = replacer.apply(varDecl.name);
                Symbol.VarSymbol newSym = new Symbol.VarSymbol(
                    varDecl.sym.flags(),
                    newName,
                    varDecl.type,
                    varDecl.sym.owner
                );
                return (T) maker.VarDef(newSym, varDecl.init);
            }
        }

        return super.translate(tree);
    }
}